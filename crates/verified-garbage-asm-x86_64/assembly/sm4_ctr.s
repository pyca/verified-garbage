// The functions of `src/sm4_ctr.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr:
	lea rsp, [rsp-3208]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+3136], rbx
	mov QWORD PTR [r9+3144], rbp
	mov QWORD PTR [r9+3152], r12
	mov QWORD PTR [r9+3160], r13
	mov QWORD PTR [r9+3168], r14
	mov QWORD PTR [r9+3176], r15
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov rbx, QWORD PTR [rsi+8]
	bswap rbx
	mov QWORD PTR [r9+3184], rax
	mov QWORD PTR [r9+3192], rbx
	add rbx, rcx
	adc rax, 0
	bswap rax
	bswap rbx
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi], rax
	mov rdx, rdx
	mov r8, rcx
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+384], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+392], r14
	movabs r14, 281470681808895
	mov QWORD PTR [r9+400], r14
	mov rsi, r9
	add rsi, 1024
	movabs r15, 16
20:
	mov rax, QWORD PTR [rdi]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	and rax, QWORD PTR [r9+384]
	mov r14, rax
	ror r14, 56
	xor rax, r14
	ror rax, 32
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	and rbx, QWORD PTR [r9+384]
	mov r14, rbx
	ror r14, 56
	xor rbx, r14
	ror rbx, 32
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	and rcx, QWORD PTR [r9+384]
	mov r14, rcx
	ror r14, 56
	xor rcx, r14
	ror rcx, 32
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	and rbp, QWORD PTR [r9+384]
	mov r14, rbp
	ror r14, 56
	xor rbp, r14
	ror rbp, 32
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	and r10, QWORD PTR [r9+384]
	mov r14, r10
	ror r14, 56
	xor r10, r14
	ror r10, 32
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	and r11, QWORD PTR [r9+384]
	mov r14, r11
	ror r14, 56
	xor r11, r14
	ror r11, 32
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	and r12, QWORD PTR [r9+384]
	mov r14, r12
	ror r14, 56
	xor r12, r14
	ror r12, 32
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	and r13, QWORD PTR [r9+384]
	mov r14, r13
	ror r14, 56
	xor r13, r14
	ror r13, 32
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	and rax, QWORD PTR [r9+392]
	mov r14, rax
	ror r14, 8
	xor rax, r14
	ror rax, 32
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	and rbx, QWORD PTR [r9+392]
	mov r14, rbx
	ror r14, 8
	xor rbx, r14
	ror rbx, 32
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	and rcx, QWORD PTR [r9+392]
	mov r14, rcx
	ror r14, 8
	xor rcx, r14
	ror rcx, 32
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	and rbp, QWORD PTR [r9+392]
	mov r14, rbp
	ror r14, 8
	xor rbp, r14
	ror rbp, 32
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	and r10, QWORD PTR [r9+392]
	mov r14, r10
	ror r14, 8
	xor r10, r14
	ror r10, 32
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	and r11, QWORD PTR [r9+392]
	mov r14, r11
	ror r14, 8
	xor r11, r14
	ror r11, 32
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	and r12, QWORD PTR [r9+392]
	mov r14, r12
	ror r14, 8
	xor r12, r14
	ror r12, 32
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	and r13, QWORD PTR [r9+392]
	mov r14, r13
	ror r14, 8
	xor r13, r14
	ror r13, 32
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	add rdi, 8
	sub r15, 1
	jne 20b
	mov rdi, r9
	add rdi, 3072
	test r8, r8
	je 21f
23:
	mov rax, QWORD PTR [r9+3184]
	mov rbx, QWORD PTR [r9+3192]
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+768], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+776], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+784], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+792], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+800], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+808], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+816], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+824], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+832], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+840], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+848], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+856], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+864], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+872], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+880], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+888], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+896], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+904], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+912], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+920], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+928], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+936], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+944], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+952], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+960], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+968], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+976], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+984], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+992], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+1000], rcx
	add rbx, 1
	adc rax, 0
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+1008], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+1016], rcx
	add rbx, 1
	adc rax, 0
	mov QWORD PTR [r9+3184], rax
	mov QWORD PTR [r9+3192], rbx
	mov rdi, r9
	movabs rsi, 392
	call {vg_sm4_crypt_prepared}
	movabs rcx, 16
	cmp r8, 16
	jb 24f
	jmp 25f
24:
	mov rcx, r8
25:
	mov rax, r9
	add rax, 768
	mov rbx, rdx
	mov r10, rcx
26:
	mov rbp, QWORD PTR [rax]
	xor rbp, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	xor rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 26b
	mov rdx, rbx
	sub r8, r10
	jne 23b
	jmp 22f
21:
22:
	mov rbx, QWORD PTR [r9+3136]
	mov rbp, QWORD PTR [r9+3144]
	mov r12, QWORD PTR [r9+3152]
	mov r13, QWORD PTR [r9+3160]
	mov r14, QWORD PTR [r9+3168]
	mov r15, QWORD PTR [r9+3176]
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
	lea rsp, [rsp+3208]
	ret
	.p2align 6
