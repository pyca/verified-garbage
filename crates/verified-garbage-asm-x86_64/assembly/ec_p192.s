// The functions of `src/ec_p192.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_public_key:
	mov r8, rdx
	mov rcx, rsi
	mov rdx, rsi
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, 0
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, 0
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -2
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, 0
	mov QWORD PTR [rdi+88], rax
	movabs rax, 1471491468346665009
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1713440714
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, 0
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
	movabs rax, 0
	mov QWORD PTR [rdi+224], rax
	movabs rax, 1
	mov QWORD PTR [rdi+232], rax
	movabs rax, 1
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, -1
	mov QWORD PTR [rdi+256], rax
	movabs rax, -5
	mov QWORD PTR [rdi+264], rax
	movabs rax, -4
	mov QWORD PTR [rdi+272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 6582798449446622100
	mov QWORD PTR [rdi+288], rax
	movabs rax, -8941764689320492195
	mov QWORD PTR [rdi+296], rax
	movabs rax, 6306562397672194216
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, -7688549487965234953
	mov QWORD PTR [rdi+320], rax
	movabs rax, -6712197403752941057
	mov QWORD PTR [rdi+328], rax
	movabs rax, -8481452413418395383
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 7649713076709468237
	mov QWORD PTR [rdi+352], rax
	movabs rax, -1928700923627975978
	mov QWORD PTR [rdi+360], rax
	movabs rax, -2440188879552712610
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 131016751202913319
	mov QWORD PTR [rdi+384], rax
	movabs rax, -2982392984492873601
	mov QWORD PTR [rdi+392], rax
	movabs rax, 1326189989267364037
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, -1471491468346665009
	mov QWORD PTR [rdi+424], rax
	movabs rax, 1713440713
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, -3
	mov QWORD PTR [rdi+448], rax
	movabs rax, -2
	mov QWORD PTR [rdi+456], rax
	movabs rax, -1
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 1471491468346665007
	mov QWORD PTR [rdi+480], rax
	movabs rax, -1713440714
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+544], rax
	movabs rax, 1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 1
	mov QWORD PTR [rdi+560], rax
	movabs rax, 0
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
	jne 20b
	mov ebx, 0
21:
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
	jne 21b
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+568], rax
	call {vg_p192_mul}
	call {vg_p192_inv_mod_p}
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
	movabs rax, -1
	mul r8
	add r9, rax
	adc r10, rdx
	adc r11, 0
	adc r12, 0
	adc r13, 0
	movabs rax, -1
	mul r8
	add r10, rax
	adc r11, rdx
	adc r12, 0
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
	movabs rax, -1
	mul r9
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	adc r8, 0
	movabs rax, -1
	mul r9
	add r11, rax
	adc r12, rdx
	adc r13, 0
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
	movabs rax, -1
	mul r10
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	adc r9, 0
	movabs rax, -1
	mul r10
	add r12, rax
	adc r13, rdx
	adc r8, 0
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
	movabs rax, -1
	mul r11
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	adc r10, 0
	movabs rax, -1
	mul r11
	add r13, rax
	adc r8, rdx
	adc r9, 0
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
	movabs rax, -1
	mul r8
	add r9, rax
	adc r10, rdx
	adc r11, 0
	adc r12, 0
	adc r13, 0
	movabs rax, -1
	mul r8
	add r10, rax
	adc r11, rdx
	adc r12, 0
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
	movabs rax, -1
	mul r9
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	adc r8, 0
	movabs rax, -1
	mul r9
	add r11, rax
	adc r12, rdx
	adc r13, 0
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
	movabs rax, -1
	mul r10
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	adc r9, 0
	movabs rax, -1
	mul r10
	add r12, rax
	adc r13, rdx
	adc r8, 0
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
	movabs rax, -1
	mul r11
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	adc r10, 0
	movabs rax, -1
	mul r11
	add r13, rax
	adc r8, rdx
	adc r9, 0
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
	mov rcx, QWORD PTR [rdi+544]
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
	movabs rax, -1
	mul r8
	add r9, rax
	adc r10, rdx
	adc r11, 0
	adc r12, 0
	adc r13, 0
	movabs rax, -1
	mul r8
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+552]
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
	movabs rax, -1
	mul r9
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	adc r8, 0
	movabs rax, -1
	mul r9
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+560]
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
	movabs rax, -1
	mul r10
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	adc r9, 0
	movabs rax, -1
	mul r10
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+568]
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
	movabs rax, -1
	mul r11
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	adc r10, 0
	movabs rax, -1
	mul r11
	add r13, rax
	adc r8, rdx
	adc r9, 0
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
	mov QWORD PTR [rdi+1280], r12
	mov QWORD PTR [rdi+1288], r13
	mov QWORD PTR [rdi+1296], r8
	mov QWORD PTR [rdi+1304], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1280]
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
	movabs rax, -1
	mul r8
	add r9, rax
	adc r10, rdx
	adc r11, 0
	adc r12, 0
	adc r13, 0
	movabs rax, -1
	mul r8
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1288]
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
	movabs rax, -1
	mul r9
	add r10, rax
	adc r11, rdx
	adc r12, 0
	adc r13, 0
	adc r8, 0
	movabs rax, -1
	mul r9
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1296]
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
	movabs rax, -1
	mul r10
	add r11, rax
	adc r12, rdx
	adc r13, 0
	adc r8, 0
	adc r9, 0
	movabs rax, -1
	mul r10
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1304]
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
	movabs rax, -1
	mul r11
	add r12, rax
	adc r13, rdx
	adc r8, 0
	adc r9, 0
	adc r10, 0
	movabs rax, -1
	mul r11
	add r13, rax
	adc r8, rdx
	adc r9, 0
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
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r8
	mov QWORD PTR [rdi+1464], r9
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
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+1184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, QWORD PTR [rdi+1208]
	and rax, rcx
	mov rax, QWORD PTR [rdi+1440]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1448]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
	mov rax, QWORD PTR [rdi+1456]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1464]
	and rax, rcx
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
