// The functions of `src/internal/vg_ecdsa_p256_verify_setup_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify_setup_adx:
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
	ret
	.p2align 6
