// The functions of `src/internal/vg_ffdh_ifma_to52_3072.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_ifma_to52_3072:
	mov r8d, 5
20:
	cmp r8, 5
	je 21f
	cmp r8, 4
	je 23f
	cmp r8, 3
	je 25f
	cmp r8, 2
	je 27f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10528
	movabs r12, 4503599627370495
	jmp 28f
27:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 512
	movabs r12, 4503599627370495
28:
	jmp 26f
25:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 992
	movabs r12, 4503599627370495
26:
	jmp 24f
23:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10016
	movabs r12, 4503599627370495
24:
	jmp 22f
21:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
22:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+320], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+448], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+360], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+456], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+256]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+256]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+264]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [rsi+264]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+272]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+400], rax
	mov rax, QWORD PTR [rsi+272]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+280]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	mov rax, QWORD PTR [rsi+280]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+288]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+464], rax
	mov rax, QWORD PTR [rsi+288]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+296]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+304]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+304]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+312]
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+312]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+320]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+320]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+328]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+336]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+336]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+344]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+344]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+352]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	mov rax, QWORD PTR [rsi+352]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+360]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	mov rax, QWORD PTR [rsi+360]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+368]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	mov rax, QWORD PTR [rsi+368]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+440], rax
	mov rax, QWORD PTR [rsi+376]
	shr rax, 60
	and rax, r12
	mov QWORD PTR [r11+472], rax
	sub r8, 1
	jne 20b
	ret
	.p2align 6
