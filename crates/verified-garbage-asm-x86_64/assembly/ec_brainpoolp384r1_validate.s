// The functions of `src/ec_brainpoolp384r1_validate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_validate_public_key:
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
