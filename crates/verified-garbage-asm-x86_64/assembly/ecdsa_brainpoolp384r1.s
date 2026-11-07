// The functions of `src/ecdsa_brainpoolp384r1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_verify:
	lea rsp, [rsp-88]
	mov r9, rsp
	add r9, 8
	cmp rdx, 48
	jb 20f
	movzx r10d, BYTE PTR [rsi]
	mov BYTE PTR [r9], r10b
	movzx r10d, BYTE PTR [rsi+1]
	mov BYTE PTR [r9+1], r10b
	movzx r10d, BYTE PTR [rsi+2]
	mov BYTE PTR [r9+2], r10b
	movzx r10d, BYTE PTR [rsi+3]
	mov BYTE PTR [r9+3], r10b
	movzx r10d, BYTE PTR [rsi+4]
	mov BYTE PTR [r9+4], r10b
	movzx r10d, BYTE PTR [rsi+5]
	mov BYTE PTR [r9+5], r10b
	movzx r10d, BYTE PTR [rsi+6]
	mov BYTE PTR [r9+6], r10b
	movzx r10d, BYTE PTR [rsi+7]
	mov BYTE PTR [r9+7], r10b
	movzx r10d, BYTE PTR [rsi+8]
	mov BYTE PTR [r9+8], r10b
	movzx r10d, BYTE PTR [rsi+9]
	mov BYTE PTR [r9+9], r10b
	movzx r10d, BYTE PTR [rsi+10]
	mov BYTE PTR [r9+10], r10b
	movzx r10d, BYTE PTR [rsi+11]
	mov BYTE PTR [r9+11], r10b
	movzx r10d, BYTE PTR [rsi+12]
	mov BYTE PTR [r9+12], r10b
	movzx r10d, BYTE PTR [rsi+13]
	mov BYTE PTR [r9+13], r10b
	movzx r10d, BYTE PTR [rsi+14]
	mov BYTE PTR [r9+14], r10b
	movzx r10d, BYTE PTR [rsi+15]
	mov BYTE PTR [r9+15], r10b
	movzx r10d, BYTE PTR [rsi+16]
	mov BYTE PTR [r9+16], r10b
	movzx r10d, BYTE PTR [rsi+17]
	mov BYTE PTR [r9+17], r10b
	movzx r10d, BYTE PTR [rsi+18]
	mov BYTE PTR [r9+18], r10b
	movzx r10d, BYTE PTR [rsi+19]
	mov BYTE PTR [r9+19], r10b
	movzx r10d, BYTE PTR [rsi+20]
	mov BYTE PTR [r9+20], r10b
	movzx r10d, BYTE PTR [rsi+21]
	mov BYTE PTR [r9+21], r10b
	movzx r10d, BYTE PTR [rsi+22]
	mov BYTE PTR [r9+22], r10b
	movzx r10d, BYTE PTR [rsi+23]
	mov BYTE PTR [r9+23], r10b
	movzx r10d, BYTE PTR [rsi+24]
	mov BYTE PTR [r9+24], r10b
	movzx r10d, BYTE PTR [rsi+25]
	mov BYTE PTR [r9+25], r10b
	movzx r10d, BYTE PTR [rsi+26]
	mov BYTE PTR [r9+26], r10b
	movzx r10d, BYTE PTR [rsi+27]
	mov BYTE PTR [r9+27], r10b
	movzx r10d, BYTE PTR [rsi+28]
	mov BYTE PTR [r9+28], r10b
	movzx r10d, BYTE PTR [rsi+29]
	mov BYTE PTR [r9+29], r10b
	movzx r10d, BYTE PTR [rsi+30]
	mov BYTE PTR [r9+30], r10b
	movzx r10d, BYTE PTR [rsi+31]
	mov BYTE PTR [r9+31], r10b
	movzx r10d, BYTE PTR [rsi+32]
	mov BYTE PTR [r9+32], r10b
	movzx r10d, BYTE PTR [rsi+33]
	mov BYTE PTR [r9+33], r10b
	movzx r10d, BYTE PTR [rsi+34]
	mov BYTE PTR [r9+34], r10b
	movzx r10d, BYTE PTR [rsi+35]
	mov BYTE PTR [r9+35], r10b
	movzx r10d, BYTE PTR [rsi+36]
	mov BYTE PTR [r9+36], r10b
	movzx r10d, BYTE PTR [rsi+37]
	mov BYTE PTR [r9+37], r10b
	movzx r10d, BYTE PTR [rsi+38]
	mov BYTE PTR [r9+38], r10b
	movzx r10d, BYTE PTR [rsi+39]
	mov BYTE PTR [r9+39], r10b
	movzx r10d, BYTE PTR [rsi+40]
	mov BYTE PTR [r9+40], r10b
	movzx r10d, BYTE PTR [rsi+41]
	mov BYTE PTR [r9+41], r10b
	movzx r10d, BYTE PTR [rsi+42]
	mov BYTE PTR [r9+42], r10b
	movzx r10d, BYTE PTR [rsi+43]
	mov BYTE PTR [r9+43], r10b
	movzx r10d, BYTE PTR [rsi+44]
	mov BYTE PTR [r9+44], r10b
	movzx r10d, BYTE PTR [rsi+45]
	mov BYTE PTR [r9+45], r10b
	movzx r10d, BYTE PTR [rsi+46]
	mov BYTE PTR [r9+46], r10b
	movzx r10d, BYTE PTR [rsi+47]
	mov BYTE PTR [r9+47], r10b
	jmp 21f
20:
	mov r10d, 0
	mov BYTE PTR [r9], r10b
	mov BYTE PTR [r9+1], r10b
	mov BYTE PTR [r9+2], r10b
	mov BYTE PTR [r9+3], r10b
	mov BYTE PTR [r9+4], r10b
	mov BYTE PTR [r9+5], r10b
	mov BYTE PTR [r9+6], r10b
	mov BYTE PTR [r9+7], r10b
	mov BYTE PTR [r9+8], r10b
	mov BYTE PTR [r9+9], r10b
	mov BYTE PTR [r9+10], r10b
	mov BYTE PTR [r9+11], r10b
	mov BYTE PTR [r9+12], r10b
	mov BYTE PTR [r9+13], r10b
	mov BYTE PTR [r9+14], r10b
	mov BYTE PTR [r9+15], r10b
	mov BYTE PTR [r9+16], r10b
	mov BYTE PTR [r9+17], r10b
	mov BYTE PTR [r9+18], r10b
	mov BYTE PTR [r9+19], r10b
	mov BYTE PTR [r9+20], r10b
	mov BYTE PTR [r9+21], r10b
	mov BYTE PTR [r9+22], r10b
	mov BYTE PTR [r9+23], r10b
	mov BYTE PTR [r9+24], r10b
	mov BYTE PTR [r9+25], r10b
	mov BYTE PTR [r9+26], r10b
	mov BYTE PTR [r9+27], r10b
	mov BYTE PTR [r9+28], r10b
	mov BYTE PTR [r9+29], r10b
	mov BYTE PTR [r9+30], r10b
	mov BYTE PTR [r9+31], r10b
	mov BYTE PTR [r9+32], r10b
	mov BYTE PTR [r9+33], r10b
	mov BYTE PTR [r9+34], r10b
	mov BYTE PTR [r9+35], r10b
	mov BYTE PTR [r9+36], r10b
	mov BYTE PTR [r9+37], r10b
	mov BYTE PTR [r9+38], r10b
	mov BYTE PTR [r9+39], r10b
	mov BYTE PTR [r9+40], r10b
	mov BYTE PTR [r9+41], r10b
	mov BYTE PTR [r9+42], r10b
	mov BYTE PTR [r9+43], r10b
	mov BYTE PTR [r9+44], r10b
	mov BYTE PTR [r9+45], r10b
	mov BYTE PTR [r9+46], r10b
	mov BYTE PTR [r9+47], r10b
	mov BYTE PTR [r9+48], r10b
	mov BYTE PTR [r9+49], r10b
	mov BYTE PTR [r9+50], r10b
	mov BYTE PTR [r9+51], r10b
	mov BYTE PTR [r9+52], r10b
	mov BYTE PTR [r9+53], r10b
	mov BYTE PTR [r9+54], r10b
	mov BYTE PTR [r9+55], r10b
	mov BYTE PTR [r9+56], r10b
	mov BYTE PTR [r9+57], r10b
	mov BYTE PTR [r9+58], r10b
	mov BYTE PTR [r9+59], r10b
	mov BYTE PTR [r9+60], r10b
	mov BYTE PTR [r9+61], r10b
	mov BYTE PTR [r9+62], r10b
	mov BYTE PTR [r9+63], r10b
	mov BYTE PTR [r9+64], r10b
	mov BYTE PTR [r9+65], r10b
	mov BYTE PTR [r9+66], r10b
	mov BYTE PTR [r9+67], r10b
	mov BYTE PTR [r9+68], r10b
	mov BYTE PTR [r9+69], r10b
	mov BYTE PTR [r9+70], r10b
	mov BYTE PTR [r9+71], r10b
	mov r11, r9
	add r11, 48
	sub r11, rdx
	test rdx, rdx
	je 22f
24:
	movzx r10d, BYTE PTR [rsi]
	mov BYTE PTR [r11], r10b
	add rsi, 1
	add r11, 1
	sub rdx, 1
	jne 24b
	jmp 23f
22:
23:
21:
	mov rsi, r9
	mov rdx, rcx
	mov rcx, r8
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
	movabs rax, -8698984072815842221
	mov QWORD PTR [rdi+64], rax
	movabs rax, -5993262882146674063
	mov QWORD PTR [rdi+72], rax
	movabs rax, 1347097566612230435
	mov QWORD PTR [rdi+80], rax
	movabs rax, 1526563086152259252
	mov QWORD PTR [rdi+88], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+96], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+104], rax
	movabs rax, 4289733633151100261
	mov QWORD PTR [rdi+112], rax
	movabs rax, -3514295694670183664
	mov QWORD PTR [rdi+120], rax
	movabs rax, 2240099277684876711
	mov QWORD PTR [rdi+128], rax
	movabs rax, 1526563086152259251
	mov QWORD PTR [rdi+136], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+144], rax
	movabs rax, -8306574491275203288
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
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+304], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+312], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+320], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+328], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+336], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+344], rax
	movabs rax, -2655231979017192295
	mov QWORD PTR [rdi+352], rax
	movabs rax, 8491523898726658171
	mov QWORD PTR [rdi+360], rax
	movabs rax, -7825160784527159884
	mov QWORD PTR [rdi+368], rax
	movabs rax, -1729406561235594380
	mov QWORD PTR [rdi+376], rax
	movabs rax, 4614658957253807200
	mov QWORD PTR [rdi+384], rax
	movabs rax, 8949637766470746321
	mov QWORD PTR [rdi+392], rax
	movabs rax, -3041344086283733004
	mov QWORD PTR [rdi+400], rax
	movabs rax, -740490093907602121
	mov QWORD PTR [rdi+408], rax
	movabs rax, 6227117305712425834
	mov QWORD PTR [rdi+416], rax
	movabs rax, 3500483756195816918
	mov QWORD PTR [rdi+424], rax
	movabs rax, 8231616977324551736
	mov QWORD PTR [rdi+432], rax
	movabs rax, 4827945035257030358
	mov QWORD PTR [rdi+440], rax
	movabs rax, -6806664257334608959
	mov QWORD PTR [rdi+448], rax
	movabs rax, 7420948023505094335
	mov QWORD PTR [rdi+456], rax
	movabs rax, -7727199590878793949
	mov QWORD PTR [rdi+464], rax
	movabs rax, 471512706623218020
	mov QWORD PTR [rdi+472], rax
	movabs rax, -7143538248096350055
	mov QWORD PTR [rdi+480], rax
	movabs rax, -8862955202463580223
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1785480228984766299
	mov QWORD PTR [rdi+496], rax
	movabs rax, -729351938195755179
	mov QWORD PTR [rdi+504], rax
	movabs rax, -539576932270393348
	mov QWORD PTR [rdi+512], rax
	movabs rax, -6809252606470155753
	mov QWORD PTR [rdi+520], rax
	movabs rax, -4173106883367674442
	mov QWORD PTR [rdi+528], rax
	movabs rax, 3239390375920101557
	mov QWORD PTR [rdi+536], rax
	movabs rax, -6030650154532004722
	mov QWORD PTR [rdi+544], rax
	movabs rax, 3973949621338336110
	mov QWORD PTR [rdi+552], rax
	movabs rax, 3067653090611193994
	mov QWORD PTR [rdi+560], rax
	movabs rax, 6289968246193342719
	mov QWORD PTR [rdi+568], rax
	movabs rax, -8104106817701388325
	mov QWORD PTR [rdi+576], rax
	movabs rax, 930156164074608578
	mov QWORD PTR [rdi+584], rax
	movabs rax, -4289733633151100261
	mov QWORD PTR [rdi+592], rax
	movabs rax, 3514295694670183663
	mov QWORD PTR [rdi+600], rax
	movabs rax, -2240099277684876712
	mov QWORD PTR [rdi+608], rax
	movabs rax, -1526563086152259252
	mov QWORD PTR [rdi+616], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+624], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+632], rax
	movabs rax, -8698984072815842223
	mov QWORD PTR [rdi+640], rax
	movabs rax, -5993262882146674063
	mov QWORD PTR [rdi+648], rax
	movabs rax, 1347097566612230435
	mov QWORD PTR [rdi+656], rax
	movabs rax, 1526563086152259252
	mov QWORD PTR [rdi+664], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+672], rax
	movabs rax, -8306574491275203288
	mov QWORD PTR [rdi+680], rax
	movabs rax, 4289733633151100259
	mov QWORD PTR [rdi+688], rax
	movabs rax, -3514295694670183664
	mov QWORD PTR [rdi+696], rax
	movabs rax, 2240099277684876711
	mov QWORD PTR [rdi+704], rax
	movabs rax, 1526563086152259251
	mov QWORD PTR [rdi+712], rax
	movabs rax, 1107163671716839903
	mov QWORD PTR [rdi+720], rax
	movabs rax, -8306574491275203288
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
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+784], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+792], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+800], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+808], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+816], rax
	movabs rax, 8306574491275203287
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
25:
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
	jne 25b
	mov ebx, 0
26:
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
	jne 26b
	mov ebx, 0
27:
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
	jne 27b
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
	movabs rax, 611627528996932574
	mov QWORD PTR [rdi+1936], rax
	movabs rax, 6004005513631619429
	mov QWORD PTR [rdi+1944], rax
	movabs rax, -8203032269463222119
	mov QWORD PTR [rdi+1952], rax
	movabs rax, 7067275440101578159
	mov QWORD PTR [rdi+1960], rax
	movabs rax, -3042481458783582932
	mov QWORD PTR [rdi+1968], rax
	movabs rax, 3944986710845028418
	mov QWORD PTR [rdi+1976], rax
	movabs rax, 2235471971536658797
	mov QWORD PTR [rdi+1984], rax
	movabs rax, 3904330365885091811
	mov QWORD PTR [rdi+1992], rax
	movabs rax, -3624176400461631782
	mov QWORD PTR [rdi+2000], rax
	movabs rax, 1675682280782692056
	mov QWORD PTR [rdi+2008], rax
	movabs rax, 3112926883013797213
	mov QWORD PTR [rdi+2016], rax
	movabs rax, 4989371539230459562
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
	call {vg_brainpoolp384r1_check_point}
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1840], r14
	mov QWORD PTR [rdi+1848], r15
	mov QWORD PTR [rdi+1856], r8
	mov QWORD PTR [rdi+1864], r9
	mov QWORD PTR [rdi+1872], r10
	mov QWORD PTR [rdi+1880], r11
	call {vg_brainpoolp384r1_inv_mod_n}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1608]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1616]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1624]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1632]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1640]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1984], r14
	mov QWORD PTR [rdi+1992], r15
	mov QWORD PTR [rdi+2000], r8
	mov QWORD PTR [rdi+2008], r9
	mov QWORD PTR [rdi+2016], r10
	mov QWORD PTR [rdi+2024], r11
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
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1560]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1568]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1936], r14
	mov QWORD PTR [rdi+1944], r15
	mov QWORD PTR [rdi+1952], r8
	mov QWORD PTR [rdi+1960], r9
	mov QWORD PTR [rdi+1968], r10
	mov QWORD PTR [rdi+1976], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2008]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2016]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+2032], r14
	mov QWORD PTR [rdi+2040], r15
	mov QWORD PTR [rdi+2048], r8
	mov QWORD PTR [rdi+2056], r9
	mov QWORD PTR [rdi+2064], r10
	mov QWORD PTR [rdi+2072], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+2080], r14
	mov QWORD PTR [rdi+2088], r15
	mov QWORD PTR [rdi+2096], r8
	mov QWORD PTR [rdi+2104], r9
	mov QWORD PTR [rdi+2112], r10
	mov QWORD PTR [rdi+2120], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov ebx, 0
28:
	movzx eax, BYTE PTR [rdi+rbx*1+1696]
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
	jne 28b
	movabs rax, 2235471971536658797
	mov QWORD PTR [rdi+1984], rax
	movabs rax, 3904330365885091811
	mov QWORD PTR [rdi+1992], rax
	movabs rax, -3624176400461631782
	mov QWORD PTR [rdi+2000], rax
	movabs rax, 1675682280782692056
	mov QWORD PTR [rdi+2008], rax
	movabs rax, 3112926883013797213
	mov QWORD PTR [rdi+2016], rax
	movabs rax, 4989371539230459562
	mov QWORD PTR [rdi+2024], rax
	movabs rax, 1063587526284971228
	mov QWORD PTR [rdi+736], rax
	movabs rax, -2109584476317797619
	mov QWORD PTR [rdi+744], rax
	movabs rax, 4871416389745276670
	mov QWORD PTR [rdi+752], rax
	movabs rax, 5324375076838120210
	mov QWORD PTR [rdi+760], rax
	movabs rax, 9070907021386418966
	mov QWORD PTR [rdi+768], rax
	movabs rax, -8740815504755015620
	mov QWORD PTR [rdi+776], rax
	movabs rax, -3932373872884052660
	mov QWORD PTR [rdi+784], rax
	movabs rax, 2719340007664735116
	mov QWORD PTR [rdi+792], rax
	movabs rax, 2580553244383960146
	mov QWORD PTR [rdi+800], rax
	movabs rax, 6061481189675467031
	mov QWORD PTR [rdi+808], rax
	movabs rax, 6865466371400505817
	mov QWORD PTR [rdi+816], rax
	movabs rax, 2011555032104603445
	mov QWORD PTR [rdi+824], rax
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+832], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+840], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+848], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+856], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+864], rax
	movabs rax, 8306574491275203287
	mov QWORD PTR [rdi+872], rax
	mov eax, 0
	mov QWORD PTR [rdi+2608], rax
	mov ebx, 55
29:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 6144
	mul rcx
	lea rdx, {VG_BRAINPOOLP384R1_COMB}
	add rdx, rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
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
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+288]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+304]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+320]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+336]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+352]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+368]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+384]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+400]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 6
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
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+640]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+656]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 9
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+768]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+784]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+800]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+816]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+832]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 10
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 11
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
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 13
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1152]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1168]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1184]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1200]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1216]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1232]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1248]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1264]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 15
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 16
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
	mov ecx, 17
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1536]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1552]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1568]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1584]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1600]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1616]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 18
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 19
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1728]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1744]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1760]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1776]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1792]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1808]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 20
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 21
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
	mov ecx, 22
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2016]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2032]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2048]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2064]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2080]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2096]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 23
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 24
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 25
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2304]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2320]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2336]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2352]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2368]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2384]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 26
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
	mov ecx, 27
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2560]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2576]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 28
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2592]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2608]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2624]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2640]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2656]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2672]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 29
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2688]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2704]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2720]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2736]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2752]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2768]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 30
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2784]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2800]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2816]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2832]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2848]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2864]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 31
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2880]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2896]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2912]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2928]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2944]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2960]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 32
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2976]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2992]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3008]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3024]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3040]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3056]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 33
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3072]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3088]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3104]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3120]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3136]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3152]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 34
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3168]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3184]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3200]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3216]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3232]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3248]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 35
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3264]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3280]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3296]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3312]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3328]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3344]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 36
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3360]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3376]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3392]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3408]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3424]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3440]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 37
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3456]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3472]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3488]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3504]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3520]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3536]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 38
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3552]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3568]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3584]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3600]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3616]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3632]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 39
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3648]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3664]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3680]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3696]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3712]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3728]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 40
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3744]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3760]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3776]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3792]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3808]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3824]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 41
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3840]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3856]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3872]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3888]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3904]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3920]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 42
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3936]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3952]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3968]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3984]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4000]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4016]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 43
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4032]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4048]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4064]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4080]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4096]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4112]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 44
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4128]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4144]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4160]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4176]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4192]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4208]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 45
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4224]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4240]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4256]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4272]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4288]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4304]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 46
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4320]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4336]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4352]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4368]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4384]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4400]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 47
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4416]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4432]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4448]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4464]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4480]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4496]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 48
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4592]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 49
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4608]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4624]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4640]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4656]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4672]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4688]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 50
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4704]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4720]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4736]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4752]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4768]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4784]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 51
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4800]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4816]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4832]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4848]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4864]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4880]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 52
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4896]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4912]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4928]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4944]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4960]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4976]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 53
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4992]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5008]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5024]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5040]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5056]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5072]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 54
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5088]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5104]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5120]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5136]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5152]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5168]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 55
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5184]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5200]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5216]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5232]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5248]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5264]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 56
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5280]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5296]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5312]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5328]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5344]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5360]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 57
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5376]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5392]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5408]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5424]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5440]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5456]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 58
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5472]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5488]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5504]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5520]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5536]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5552]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 59
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5568]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5584]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5600]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5616]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5632]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5648]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 60
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5664]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5680]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5696]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5712]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5728]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5744]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 61
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5760]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5776]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5792]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5808]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5824]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5840]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 62
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5856]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5872]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5888]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5904]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5920]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5936]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 63
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5952]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5968]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5984]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6000]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6016]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6032]
	pand xmm14, xmm15
	por xmm5, xmm14
	mov ecx, 64
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6048]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6064]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6080]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6096]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6112]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6128]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu XMMWORD PTR [rdi+1104], xmm5
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 8698984072815842221
	and rax, rcx
	or rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 5993262882146674062
	and rax, rcx
	or rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -1347097566612230436
	and rax, rcx
	or rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -1526563086152259253
	and rax, rcx
	or rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1096], rax
	movabs rax, -1107163671716839904
	and rax, rcx
	or rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 8306574491275203287
	and rax, rcx
	or rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1112], rax
	xor rcx, -1
	movabs rax, 8698984072815842221
	and rax, rcx
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 5993262882146674062
	and rax, rcx
	mov QWORD PTR [rdi+1128], rax
	movabs rax, -1347097566612230436
	and rax, rcx
	mov QWORD PTR [rdi+1136], rax
	movabs rax, -1526563086152259253
	and rax, rcx
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1107163671716839904
	and rax, rcx
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 8306574491275203287
	and rax, rcx
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
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1504], r8
	mov QWORD PTR [rdi+1512], r9
	mov QWORD PTR [rdi+1520], r10
	mov QWORD PTR [rdi+1528], r11
	mov QWORD PTR [rdi+1536], r12
	mov QWORD PTR [rdi+1544], r13
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2230]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1088]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1096]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1104]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1112]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	movabs rax, -3041344086283733004
	mov QWORD PTR [rdi+1504], rax
	movabs rax, -740490093907602121
	mov QWORD PTR [rdi+1512], rax
	movabs rax, 6227117305712425834
	mov QWORD PTR [rdi+1520], rax
	movabs rax, 3500483756195816918
	mov QWORD PTR [rdi+1528], rax
	movabs rax, 8231616977324551736
	mov QWORD PTR [rdi+1536], rax
	movabs rax, 4827945035257030358
	mov QWORD PTR [rdi+1544], rax
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
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+792]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
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
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+872]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
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
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1072]
	adc r9, QWORD PTR [rdi+1080]
	adc r10, QWORD PTR [rdi+1088]
	adc r11, QWORD PTR [rdi+1096]
	adc r12, QWORD PTR [rdi+1104]
	adc r13, QWORD PTR [rdi+1112]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1120]
	adc r9, QWORD PTR [rdi+1128]
	adc r10, QWORD PTR [rdi+1136]
	adc r11, QWORD PTR [rdi+1144]
	adc r12, QWORD PTR [rdi+1152]
	adc r13, QWORD PTR [rdi+1160]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1120]
	adc r9, QWORD PTR [rdi+1128]
	adc r10, QWORD PTR [rdi+1136]
	adc r11, QWORD PTR [rdi+1144]
	adc r12, QWORD PTR [rdi+1152]
	adc r13, QWORD PTR [rdi+1160]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+976]
	sbb r9, QWORD PTR [rdi+984]
	sbb r10, QWORD PTR [rdi+992]
	sbb r11, QWORD PTR [rdi+1000]
	sbb r12, QWORD PTR [rdi+1008]
	sbb r13, QWORD PTR [rdi+1016]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r14
	mov QWORD PTR [rdi+936], r15
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov QWORD PTR [rdi+960], r10
	mov QWORD PTR [rdi+968], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1504]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12, QWORD PTR [rdi+960]
	mov r13, QWORD PTR [rdi+968]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
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
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8, QWORD PTR [rdi+976]
	mov r9, QWORD PTR [rdi+984]
	mov r10, QWORD PTR [rdi+992]
	mov r11, QWORD PTR [rdi+1000]
	mov r12, QWORD PTR [rdi+1008]
	mov r13, QWORD PTR [rdi+1016]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2230]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2229]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2228]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2227]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2226]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2225]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2224]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+880]
	mov rdx, QWORD PTR [rdi+736]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov rdx, QWORD PTR [rdi+744]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov rdx, QWORD PTR [rdi+752]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov rdx, QWORD PTR [rdi+760]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov rdx, QWORD PTR [rdi+768]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov rdx, QWORD PTR [rdi+776]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov rdx, QWORD PTR [rdi+784]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov rdx, QWORD PTR [rdi+792]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov rdx, QWORD PTR [rdi+800]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov rdx, QWORD PTR [rdi+808]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov rdx, QWORD PTR [rdi+816]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov rdx, QWORD PTR [rdi+824]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov rdx, QWORD PTR [rdi+832]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov rdx, QWORD PTR [rdi+840]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+848]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+856]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+864]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+872]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+872], rax
	test rbx, rbx
	jne 29b
	mov rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+2040], rax
	mov rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+2072], rax
	mov rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+2080], rax
	mov rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+2088], rax
	mov rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+2096], rax
	mov rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+2104], rax
	mov rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+2112], rax
	mov rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+2120], rax
	mov rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+1840], rax
	mov rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+1848], rax
	mov rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+1856], rax
	mov rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+1864], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+1872], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+1880], rax
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
	movabs rax, 8698984072815842221
	mov QWORD PTR [rdi+784], rax
	movabs rax, 5993262882146674062
	mov QWORD PTR [rdi+792], rax
	movabs rax, -1347097566612230436
	mov QWORD PTR [rdi+800], rax
	movabs rax, -1526563086152259253
	mov QWORD PTR [rdi+808], rax
	movabs rax, -1107163671716839904
	mov QWORD PTR [rdi+816], rax
	movabs rax, 8306574491275203287
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
	mov ebx, 0
210:
	movzx eax, BYTE PTR [rdi+rbx*1+1744]
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
	jne 210b
	mov ebx, 384
211:
	sub rbx, 1
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
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+792]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
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
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+872]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
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
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+976]
	sbb r9, QWORD PTR [rdi+984]
	sbb r10, QWORD PTR [rdi+992]
	sbb r11, QWORD PTR [rdi+1000]
	sbb r12, QWORD PTR [rdi+1008]
	sbb r13, QWORD PTR [rdi+1016]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r14
	mov QWORD PTR [rdi+936], r15
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov QWORD PTR [rdi+960], r10
	mov QWORD PTR [rdi+968], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12, QWORD PTR [rdi+960]
	mov r13, QWORD PTR [rdi+968]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
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
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8, QWORD PTR [rdi+976]
	mov r9, QWORD PTR [rdi+984]
	mov r10, QWORD PTR [rdi+992]
	mov r11, QWORD PTR [rdi+1000]
	mov r12, QWORD PTR [rdi+1008]
	mov r13, QWORD PTR [rdi+1016]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+992]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1000]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1008]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1016]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+312]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+320]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+328]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+336]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+344]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+928]
	adc r9, QWORD PTR [rdi+936]
	adc r10, QWORD PTR [rdi+944]
	adc r11, QWORD PTR [rdi+952]
	adc r12, QWORD PTR [rdi+960]
	adc r13, QWORD PTR [rdi+968]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2128]
	adc r9, QWORD PTR [rdi+2136]
	adc r10, QWORD PTR [rdi+2144]
	adc r11, QWORD PTR [rdi+2152]
	adc r12, QWORD PTR [rdi+2160]
	adc r13, QWORD PTR [rdi+2168]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+304]
	adc r9, QWORD PTR [rdi+312]
	adc r10, QWORD PTR [rdi+320]
	adc r11, QWORD PTR [rdi+328]
	adc r12, QWORD PTR [rdi+336]
	adc r13, QWORD PTR [rdi+344]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12, QWORD PTR [rdi+960]
	mov r13, QWORD PTR [rdi+968]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+2128]
	mov r9, QWORD PTR [rdi+2136]
	mov r10, QWORD PTR [rdi+2144]
	mov r11, QWORD PTR [rdi+2152]
	mov r12, QWORD PTR [rdi+2160]
	mov r13, QWORD PTR [rdi+2168]
	mov r14d, 0
	add r8, QWORD PTR [rdi+304]
	adc r9, QWORD PTR [rdi+312]
	adc r10, QWORD PTR [rdi+320]
	adc r11, QWORD PTR [rdi+328]
	adc r12, QWORD PTR [rdi+336]
	adc r13, QWORD PTR [rdi+344]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
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
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1120], r14
	mov QWORD PTR [rdi+1128], r15
	mov QWORD PTR [rdi+1136], r8
	mov QWORD PTR [rdi+1144], r9
	mov QWORD PTR [rdi+1152], r10
	mov QWORD PTR [rdi+1160], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r14
	mov QWORD PTR [rdi+1032], r15
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	mov QWORD PTR [rdi+1056], r10
	mov QWORD PTR [rdi+1064], r11
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1120]
	adc r9, QWORD PTR [rdi+1128]
	adc r10, QWORD PTR [rdi+1136]
	adc r11, QWORD PTR [rdi+1144]
	adc r12, QWORD PTR [rdi+1152]
	adc r13, QWORD PTR [rdi+1160]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1120], r8
	mov QWORD PTR [rdi+1128], r9
	mov QWORD PTR [rdi+1136], r10
	mov QWORD PTR [rdi+1144], r11
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+1120]
	sbb r9, QWORD PTR [rdi+1128]
	sbb r10, QWORD PTR [rdi+1136]
	sbb r11, QWORD PTR [rdi+1144]
	sbb r12, QWORD PTR [rdi+1152]
	sbb r13, QWORD PTR [rdi+1160]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1120]
	adc r9, QWORD PTR [rdi+1128]
	adc r10, QWORD PTR [rdi+1136]
	adc r11, QWORD PTR [rdi+1144]
	adc r12, QWORD PTR [rdi+1152]
	adc r13, QWORD PTR [rdi+1160]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1120], r8
	mov QWORD PTR [rdi+1128], r9
	mov QWORD PTR [rdi+1136], r10
	mov QWORD PTR [rdi+1144], r11
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
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
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r14
	mov QWORD PTR [rdi+1032], r15
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	mov QWORD PTR [rdi+1056], r10
	mov QWORD PTR [rdi+1064], r11
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
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
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1120], r14
	mov QWORD PTR [rdi+1128], r15
	mov QWORD PTR [rdi+1136], r8
	mov QWORD PTR [rdi+1144], r9
	mov QWORD PTR [rdi+1152], r10
	mov QWORD PTR [rdi+1160], r11
	mov r8, QWORD PTR [rdi+1120]
	mov r9, QWORD PTR [rdi+1128]
	mov r10, QWORD PTR [rdi+1136]
	mov r11, QWORD PTR [rdi+1144]
	mov r12, QWORD PTR [rdi+1152]
	mov r13, QWORD PTR [rdi+1160]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1120], r8
	mov QWORD PTR [rdi+1128], r9
	mov QWORD PTR [rdi+1136], r10
	mov QWORD PTR [rdi+1144], r11
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	movzx eax, BYTE PTR [rdi+rbx*1+2224]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+880]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov rdx, QWORD PTR [rdi+1056]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov rdx, QWORD PTR [rdi+1064]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+872], rax
	test rbx, rbx
	jne 211b
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+2080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+2088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+2096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r14
	mov QWORD PTR [rdi+1224], r15
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov QWORD PTR [rdi+1248], r10
	mov QWORD PTR [rdi+1256], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1872]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2080]
	adc r9, QWORD PTR [rdi+2088]
	adc r10, QWORD PTR [rdi+2096]
	adc r11, QWORD PTR [rdi+2104]
	adc r12, QWORD PTR [rdi+2112]
	adc r13, QWORD PTR [rdi+2120]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
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
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	sub r8, QWORD PTR [rdi+1360]
	sbb r9, QWORD PTR [rdi+1368]
	sbb r10, QWORD PTR [rdi+1376]
	sbb r11, QWORD PTR [rdi+1384]
	sbb r12, QWORD PTR [rdi+1392]
	sbb r13, QWORD PTR [rdi+1400]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1840]
	adc r9, QWORD PTR [rdi+1848]
	adc r10, QWORD PTR [rdi+1856]
	adc r11, QWORD PTR [rdi+1864]
	adc r12, QWORD PTR [rdi+1872]
	adc r13, QWORD PTR [rdi+1880]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb r12, QWORD PTR [rdi+1440]
	sbb r13, QWORD PTR [rdi+1448]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1840]
	adc r9, QWORD PTR [rdi+1848]
	adc r10, QWORD PTR [rdi+1856]
	adc r11, QWORD PTR [rdi+1864]
	adc r12, QWORD PTR [rdi+1872]
	adc r13, QWORD PTR [rdi+1880]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
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
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+880]
	sbb r9, QWORD PTR [rdi+888]
	sbb r10, QWORD PTR [rdi+896]
	sbb r11, QWORD PTR [rdi+904]
	sbb r12, QWORD PTR [rdi+912]
	sbb r13, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	sub r8, QWORD PTR [rdi+976]
	sbb r9, QWORD PTR [rdi+984]
	sbb r10, QWORD PTR [rdi+992]
	sbb r11, QWORD PTR [rdi+1000]
	sbb r12, QWORD PTR [rdi+1008]
	sbb r13, QWORD PTR [rdi+1016]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+976]
	adc r9, QWORD PTR [rdi+984]
	adc r10, QWORD PTR [rdi+992]
	adc r11, QWORD PTR [rdi+1000]
	adc r12, QWORD PTR [rdi+1008]
	adc r13, QWORD PTR [rdi+1016]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+880]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r14
	mov QWORD PTR [rdi+936], r15
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov QWORD PTR [rdi+960], r10
	mov QWORD PTR [rdi+968], r11
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
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
	mov rcx, QWORD PTR [rdi+352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1360]
	mov r9, QWORD PTR [rdi+1368]
	mov r10, QWORD PTR [rdi+1376]
	mov r11, QWORD PTR [rdi+1384]
	mov r12, QWORD PTR [rdi+1392]
	mov r13, QWORD PTR [rdi+1400]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12, QWORD PTR [rdi+960]
	mov r13, QWORD PTR [rdi+968]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1360]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+880]
	mov r9, QWORD PTR [rdi+888]
	mov r10, QWORD PTR [rdi+896]
	mov r11, QWORD PTR [rdi+904]
	mov r12, QWORD PTR [rdi+912]
	mov r13, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov QWORD PTR [rdi+896], r10
	mov QWORD PTR [rdi+904], r11
	mov QWORD PTR [rdi+912], r12
	mov QWORD PTR [rdi+920], r13
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
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov QWORD PTR [rdi+992], r8
	mov QWORD PTR [rdi+1000], r9
	mov QWORD PTR [rdi+1008], r10
	mov QWORD PTR [rdi+1016], r11
	mov r8, QWORD PTR [rdi+976]
	mov r9, QWORD PTR [rdi+984]
	mov r10, QWORD PTR [rdi+992]
	mov r11, QWORD PTR [rdi+1000]
	mov r12, QWORD PTR [rdi+1008]
	mov r13, QWORD PTR [rdi+1016]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r13
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r14
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+4048]
	cmovae r9, QWORD PTR [rdi+4056]
	cmovae r10, QWORD PTR [rdi+4064]
	cmovae r11, QWORD PTR [rdi+4072]
	cmovae r12, QWORD PTR [rdi+4080]
	cmovae r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov QWORD PTR [rdi+992], r10
	mov QWORD PTR [rdi+1000], r11
	mov QWORD PTR [rdi+1008], r12
	mov QWORD PTR [rdi+1016], r13
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+872], rax
	call {vg_brainpoolp384r1_inv_mod_p}
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
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1696]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1704]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1712]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+256]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+264]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+272]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+280]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+288]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+296]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, -7318726059172640731
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1744], r14
	mov QWORD PTR [rdi+1752], r15
	mov QWORD PTR [rdi+1760], r8
	mov QWORD PTR [rdi+1768], r9
	mov QWORD PTR [rdi+1776], r10
	mov QWORD PTR [rdi+1784], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rax, r8
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r13
	movabs rcx, 6701036469587655571
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+128]
	mul rcx
	add r15, rax
	adc rdx, 0
	add r15, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+136]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rax, r14
	sub rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+4048], rax
	mov rax, r15
	sbb rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+4056], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+4064], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+4072], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+4080], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+4088], rax
	mov rax, r12
	sbb rax, 0
	cmovae r14, QWORD PTR [rdi+4048]
	cmovae r15, QWORD PTR [rdi+4056]
	cmovae r8, QWORD PTR [rdi+4064]
	cmovae r9, QWORD PTR [rdi+4072]
	cmovae r10, QWORD PTR [rdi+4080]
	cmovae r11, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1888], r14
	mov QWORD PTR [rdi+1896], r15
	mov QWORD PTR [rdi+1904], r8
	mov QWORD PTR [rdi+1912], r9
	mov QWORD PTR [rdi+1920], r10
	mov QWORD PTR [rdi+1928], r11
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	sub r8, QWORD PTR [rdi+1936]
	sbb r9, QWORD PTR [rdi+1944]
	sbb r10, QWORD PTR [rdi+1952]
	sbb r11, QWORD PTR [rdi+1960]
	sbb r12, QWORD PTR [rdi+1968]
	sbb r13, QWORD PTR [rdi+1976]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+4048], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+128]
	and rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	mov rdx, QWORD PTR [rdi+136]
	and rdx, rax
	mov QWORD PTR [rdi+4072], rdx
	mov rdx, QWORD PTR [rdi+144]
	and rdx, rax
	mov QWORD PTR [rdi+4080], rdx
	mov rdx, QWORD PTR [rdi+152]
	and rdx, rax
	mov QWORD PTR [rdi+4088], rdx
	add r8, QWORD PTR [rdi+4048]
	adc r9, QWORD PTR [rdi+4056]
	adc r10, QWORD PTR [rdi+4064]
	adc r11, QWORD PTR [rdi+4072]
	adc r12, QWORD PTR [rdi+4080]
	adc r13, QWORD PTR [rdi+4088]
	mov QWORD PTR [rdi+1984], r8
	mov QWORD PTR [rdi+1992], r9
	mov QWORD PTR [rdi+2000], r10
	mov QWORD PTR [rdi+2008], r11
	mov QWORD PTR [rdi+2016], r12
	mov QWORD PTR [rdi+2024], r13
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
	mov rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	or rdx, QWORD PTR [rdi+2008]
	or rdx, QWORD PTR [rdi+2016]
	or rdx, QWORD PTR [rdi+2024]
	cmp rdx, 1
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
	lea rsp, [rsp+88]
	ret
	.p2align 6

vg_ecdsa_brainpoolp384r1_sign:
	mov rcx, r8
	mov r10, QWORD PTR [r9+32]
	mov r11, QWORD PTR [r9+40]
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push r11
	push r10
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	xor eax, eax
	mov QWORD PTR [rsp+320], rax
	xor eax, eax
	mov QWORD PTR [rsp+328], rax
	xor eax, eax
	mov QWORD PTR [rsp+336], rax
	xor eax, eax
	mov QWORD PTR [rsp+344], rax
	xor eax, eax
	mov QWORD PTR [rsp+352], rax
	xor eax, eax
	mov QWORD PTR [rsp+360], rax
	xor eax, eax
	mov QWORD PTR [rsp+368], rax
	xor eax, eax
	mov QWORD PTR [rsp+376], rax
	xor eax, eax
	mov QWORD PTR [rsp+384], rax
	mov rcx, QWORD PTR [rsp+216]
	mov eax, 48
	cmp rcx, rax
	cmovae rcx, rax
	mov rdi, rsp
	add rdi, 368
	sub rdi, rcx
	mov rsi, QWORD PTR [rsp+192]
	xor r8d, r8d
20:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, rcx
	jne 20b
	mov rsi, rsp
	add rsi, 320
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, 4289733633151100261
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -3514295694670183664
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, 2240099277684876711
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, 1526563086152259251
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+96], rax
	movabs rdx, 1107163671716839903
	sbb rax, rdx
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+104], rax
	movabs rdx, -8306574491275203288
	sbb rax, rdx
	mov QWORD PTR [rsp+40], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+272], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsp+96]
	mov rcx, QWORD PTR [rsp+32]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+104]
	mov rcx, QWORD PTR [rsp+40]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+248], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov eax, 0
	mov BYTE PTR [rdi+2256], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2257], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2265], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2273], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2281], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	add rsi, QWORD PTR [rsp+216]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 97
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 0
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov eax, 1
	mov BYTE PTR [rdi+2256], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2257], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2265], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2273], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2281], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	add rsi, QWORD PTR [rsp+216]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 97
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 0
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov eax, 128
	mov QWORD PTR [rsp+176], rax
21:
	xor eax, eax
	mov QWORD PTR [rsp+128], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 0
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, rsp
	add rsi, 64
	mov rdi, rsp
	add rdi, 464
	add rdi, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+216]
	xor r8d, r8d
23:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, rcx
	jne 23b
	mov rax, QWORD PTR [rsp+128]
	add rax, QWORD PTR [rsp+216]
	mov QWORD PTR [rsp+128], rax
	cmp rax, 48
	jb 22b
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 320
	mov rcx, rsp
	add rcx, 464
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_brainpoolp384r1_sign_k}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 24f
	xor edx, edx
	jmp 25f
24:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov eax, 0
	mov BYTE PTR [rdi+2256], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	add rsi, QWORD PTR [rsp+216]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 1
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 1
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+216]
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, QWORD PTR [rsp+224]
	add rdx, QWORD PTR [rsp+216]
	add rdx, 0
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	mov r11, QWORD PTR [rsp+600]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov edx, 1
	test rdx, rdx
25:
	jne 21b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rcx
	mov QWORD PTR [rsp+376], rcx
	mov QWORD PTR [rsp+384], rcx
	mov QWORD PTR [rsp+392], rcx
	mov QWORD PTR [rsp+400], rcx
	mov QWORD PTR [rsp+408], rcx
	mov QWORD PTR [rsp+416], rcx
	mov QWORD PTR [rsp+424], rcx
	mov QWORD PTR [rsp+432], rcx
	mov QWORD PTR [rsp+440], rcx
	mov QWORD PTR [rsp+448], rcx
	mov QWORD PTR [rsp+456], rcx
	mov QWORD PTR [rsp+464], rcx
	mov QWORD PTR [rsp+472], rcx
	mov QWORD PTR [rsp+480], rcx
	mov QWORD PTR [rsp+488], rcx
	mov QWORD PTR [rsp+496], rcx
	mov QWORD PTR [rsp+504], rcx
	mov QWORD PTR [rsp+512], rcx
	mov QWORD PTR [rsp+520], rcx
	mov QWORD PTR [rsp+528], rcx
	mov QWORD PTR [rsp+536], rcx
	mov QWORD PTR [rsp+544], rcx
	mov QWORD PTR [rsp+552], rcx
	mov QWORD PTR [rsp+560], rcx
	mov QWORD PTR [rsp+568], rcx
	mov QWORD PTR [rsp+576], rcx
	mov QWORD PTR [rsp+584], rcx
	mov QWORD PTR [rsp+592], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	ret
	.p2align 6
