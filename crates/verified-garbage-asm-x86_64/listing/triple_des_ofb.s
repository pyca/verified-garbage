// The functions of `src/triple_des_ofb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ofb:
	lea rsp, [rsp-976]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+904], rbx
	mov QWORD PTR [r9+912], rbp
	mov QWORD PTR [r9+920], r12
	mov QWORD PTR [r9+928], r13
	mov QWORD PTR [r9+936], r14
	mov QWORD PTR [r9+944], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+520], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+528], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+536], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+544], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+552], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+560], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+568], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+576], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+584], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+592], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+600], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+608], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+616], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+624], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+632], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+640], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [r9+648], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [r9+656], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [r9+664], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [r9+672], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [r9+680], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [r9+688], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [r9+696], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [r9+704], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [r9+712], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [r9+720], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [r9+728], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [r9+736], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [r9+744], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [r9+752], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+760], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+768], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+776], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+784], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [r9+792], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [r9+800], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [r9+808], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [r9+816], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [r9+824], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [r9+832], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [r9+840], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [r9+848], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [r9+856], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [r9+864], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [r9+872], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [r9+880], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [r9+888], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [r9+896], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+512], rbp
	test r13, r13
	je 20f
22:
	mov rdi, r9
	add rdi, 520
	mov rsi, r9
	add rsi, 512
	mov rdx, r9
	call {vg_triple_des_encrypt_block}
	mov r9, rdx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r12], rax
	add r12, 8
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+512]
	mov QWORD PTR [rax], rbp
	mov rbx, QWORD PTR [r9+904]
	mov rbp, QWORD PTR [r9+912]
	mov r12, QWORD PTR [r9+920]
	mov r13, QWORD PTR [r9+928]
	mov r14, QWORD PTR [r9+936]
	mov r15, QWORD PTR [r9+944]
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
	lea rsp, [rsp+976]
	ret
	.p2align 6
