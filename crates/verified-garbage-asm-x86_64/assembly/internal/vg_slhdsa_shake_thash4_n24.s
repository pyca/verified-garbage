// The functions of `src/internal/vg_slhdsa_shake_thash4_n24.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_thash4_n24:
	mov eax, 0
	mov QWORD PTR [r8], rax
	mov QWORD PTR [r8+8], rax
	mov QWORD PTR [r8+16], rax
	mov QWORD PTR [r8+24], rax
	mov QWORD PTR [r8+32], rax
	mov QWORD PTR [r8+40], rax
	mov QWORD PTR [r8+48], rax
	mov QWORD PTR [r8+56], rax
	mov QWORD PTR [r8+64], rax
	mov QWORD PTR [r8+72], rax
	mov QWORD PTR [r8+80], rax
	mov QWORD PTR [r8+88], rax
	mov QWORD PTR [r8+96], rax
	mov QWORD PTR [r8+104], rax
	mov QWORD PTR [r8+112], rax
	mov QWORD PTR [r8+120], rax
	mov QWORD PTR [r8+128], rax
	mov QWORD PTR [r8+136], rax
	mov QWORD PTR [r8+144], rax
	mov QWORD PTR [r8+152], rax
	mov QWORD PTR [r8+160], rax
	mov QWORD PTR [r8+168], rax
	mov QWORD PTR [r8+176], rax
	mov QWORD PTR [r8+184], rax
	mov QWORD PTR [r8+192], rax
	mov QWORD PTR [r8+200], rax
	mov QWORD PTR [r8+208], rax
	mov QWORD PTR [r8+216], rax
	mov QWORD PTR [r8+224], rax
	mov QWORD PTR [r8+232], rax
	mov QWORD PTR [r8+240], rax
	mov QWORD PTR [r8+248], rax
	mov QWORD PTR [r8+256], rax
	mov QWORD PTR [r8+264], rax
	mov QWORD PTR [r8+272], rax
	mov QWORD PTR [r8+280], rax
	mov QWORD PTR [r8+288], rax
	mov QWORD PTR [r8+296], rax
	mov QWORD PTR [r8+304], rax
	mov QWORD PTR [r8+312], rax
	mov QWORD PTR [r8+320], rax
	mov QWORD PTR [r8+328], rax
	mov QWORD PTR [r8+336], rax
	mov QWORD PTR [r8+344], rax
	mov QWORD PTR [r8+352], rax
	mov QWORD PTR [r8+360], rax
	mov QWORD PTR [r8+368], rax
	mov QWORD PTR [r8+376], rax
	mov QWORD PTR [r8+384], rax
	mov QWORD PTR [r8+392], rax
	mov QWORD PTR [r8+400], rax
	mov QWORD PTR [r8+408], rax
	mov QWORD PTR [r8+416], rax
	mov QWORD PTR [r8+424], rax
	mov QWORD PTR [r8+432], rax
	mov QWORD PTR [r8+440], rax
	mov QWORD PTR [r8+448], rax
	mov QWORD PTR [r8+456], rax
	mov QWORD PTR [r8+464], rax
	mov QWORD PTR [r8+472], rax
	mov QWORD PTR [r8+480], rax
	mov QWORD PTR [r8+488], rax
	mov QWORD PTR [r8+496], rax
	mov QWORD PTR [r8+504], rax
	mov QWORD PTR [r8+512], rax
	mov QWORD PTR [r8+520], rax
	mov QWORD PTR [r8+528], rax
	mov QWORD PTR [r8+536], rax
	mov QWORD PTR [r8+544], rax
	mov QWORD PTR [r8+552], rax
	mov QWORD PTR [r8+560], rax
	mov QWORD PTR [r8+568], rax
	mov QWORD PTR [r8+576], rax
	mov QWORD PTR [r8+584], rax
	mov QWORD PTR [r8+592], rax
	mov QWORD PTR [r8+600], rax
	mov QWORD PTR [r8+608], rax
	mov QWORD PTR [r8+616], rax
	mov QWORD PTR [r8+624], rax
	mov QWORD PTR [r8+632], rax
	mov QWORD PTR [r8+640], rax
	mov QWORD PTR [r8+648], rax
	mov QWORD PTR [r8+656], rax
	mov QWORD PTR [r8+664], rax
	mov QWORD PTR [r8+672], rax
	mov QWORD PTR [r8+680], rax
	mov QWORD PTR [r8+688], rax
	mov QWORD PTR [r8+696], rax
	mov QWORD PTR [r8+704], rax
	mov QWORD PTR [r8+712], rax
	mov QWORD PTR [r8+720], rax
	mov QWORD PTR [r8+728], rax
	mov QWORD PTR [r8+736], rax
	mov QWORD PTR [r8+744], rax
	mov QWORD PTR [r8+752], rax
	mov QWORD PTR [r8+760], rax
	mov QWORD PTR [r8+768], rax
	mov QWORD PTR [r8+776], rax
	mov QWORD PTR [r8+784], rax
	mov QWORD PTR [r8+792], rax
	mov r9, rdi
	add r9, rsi
	mov r10, r9
	add r10, rsi
	mov r11, r10
	add r11, rsi
	mov esi, 0
	mov ecx, 0
20:
	mov rax, QWORD PTR [rdi+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1]
	mov QWORD PTR [r8+rcx*1], rax
	mov rax, QWORD PTR [r9+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+8]
	mov QWORD PTR [r8+rcx*1+8], rax
	mov rax, QWORD PTR [r10+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+16]
	mov QWORD PTR [r8+rcx*1+16], rax
	mov rax, QWORD PTR [r11+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+24]
	mov QWORD PTR [r8+rcx*1+24], rax
	add rsi, 8
	add rcx, 32
	sub rdx, 8
	cmp rcx, 544
	je 21f
	jmp 22f
21:
	mov QWORD PTR [r8+2368], rdi
	mov QWORD PTR [r8+2376], rdx
	mov QWORD PTR [r8+2384], rsi
	mov rdi, r8
	mov rsi, r8
	add rsi, 800
	mov rdx, r8
	add rdx, 1600
	mov rcx, r8
	add rcx, 2368
	movq xmm8, r9
	movq xmm9, r10
	movq xmm10, r11
	mov rax, QWORD PTR [r8+2368]
	movq xmm11, rax
	mov rax, QWORD PTR [r8+2376]
	movq xmm12, rax
	mov rax, QWORD PTR [r8+2384]
	movq xmm13, rax
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+32]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+64]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+96]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+128]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+160]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+192]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+224]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+256]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+288]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+320]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+352]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+384]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+416]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+448]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+480]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+512]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+544]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+576]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+608]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+640]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+672]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+704]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+736]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+768]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+32], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+64], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+96], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+128], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+160], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+192], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+224], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+256], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+288], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+320], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+352], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+384], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+416], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+448], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+480], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+512], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+544], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+576], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+608], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+640], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+672], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+704], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+736], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+768], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+40]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+72]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+104]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+136]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+168]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+200]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+232]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+264]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+296]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+328]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+360]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+392]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+424]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+456]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+488]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+520]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+552]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+584]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+616]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+648]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+680]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+712]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+744]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+776]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+40], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+72], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+104], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+136], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+168], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+200], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+232], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+264], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+296], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+328], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+360], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+392], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+424], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+456], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+488], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+520], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+552], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+584], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+616], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+648], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+680], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+712], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+744], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+776], rax
	mov rax, QWORD PTR [r8+16]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+48]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+80]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+112]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+144]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+176]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+208]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+240]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+272]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+304]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+336]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+368]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+400]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+432]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+464]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+496]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+528]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+560]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+592]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+624]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+656]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+688]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+720]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+752]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+784]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+16], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+48], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+80], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+112], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+144], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+176], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+208], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+240], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+272], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+304], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+336], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+368], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+400], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+432], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+464], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+496], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+528], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+560], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+592], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+624], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+656], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+688], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+720], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+752], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+784], rax
	mov rax, QWORD PTR [r8+24]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+56]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+88]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+120]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+152]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+184]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+216]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+248]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+280]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+312]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+344]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+376]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+408]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+440]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+472]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+504]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+536]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+568]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+600]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+632]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+664]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+696]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+728]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+760]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+792]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+24], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+56], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+88], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+120], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+152], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+184], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+216], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+248], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+280], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+312], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+344], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+376], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+408], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+440], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+472], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+504], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+536], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+568], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+600], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+632], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+664], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+696], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+728], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+760], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+792], rax
	movq r9, xmm8
	movq r10, xmm9
	movq r11, xmm10
	movq rax, xmm11
	mov QWORD PTR [r8+2368], rax
	movq rax, xmm12
	mov QWORD PTR [r8+2376], rax
	movq rax, xmm13
	mov QWORD PTR [r8+2384], rax
	mov rdi, QWORD PTR [r8+2368]
	mov rdx, QWORD PTR [r8+2376]
	mov rsi, QWORD PTR [r8+2384]
	mov ecx, 0
22:
	test rdx, rdx
	jne 20b
	movabs rsi, -9223372036854775808
	mov rax, QWORD PTR [r8+rcx*1]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1], rax
	mov rax, QWORD PTR [r8+512]
	xor rax, rsi
	mov QWORD PTR [r8+512], rax
	mov rax, QWORD PTR [r8+rcx*1+8]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+8], rax
	mov rax, QWORD PTR [r8+520]
	xor rax, rsi
	mov QWORD PTR [r8+520], rax
	mov rax, QWORD PTR [r8+rcx*1+16]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+16], rax
	mov rax, QWORD PTR [r8+528]
	xor rax, rsi
	mov QWORD PTR [r8+528], rax
	mov rax, QWORD PTR [r8+rcx*1+24]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+24], rax
	mov rax, QWORD PTR [r8+536]
	xor rax, rsi
	mov QWORD PTR [r8+536], rax
	mov QWORD PTR [r8+2368], rdi
	mov QWORD PTR [r8+2376], rdx
	mov QWORD PTR [r8+2384], rsi
	mov rdi, r8
	mov rsi, r8
	add rsi, 800
	mov rdx, r8
	add rdx, 1600
	mov rcx, r8
	add rcx, 2368
	movq xmm8, r9
	movq xmm9, r10
	movq xmm10, r11
	mov rax, QWORD PTR [r8+2368]
	movq xmm11, rax
	mov rax, QWORD PTR [r8+2376]
	movq xmm12, rax
	mov rax, QWORD PTR [r8+2384]
	movq xmm13, rax
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+32]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+64]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+96]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+128]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+160]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+192]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+224]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+256]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+288]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+320]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+352]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+384]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+416]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+448]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+480]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+512]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+544]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+576]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+608]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+640]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+672]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+704]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+736]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+768]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+32], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+64], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+96], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+128], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+160], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+192], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+224], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+256], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+288], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+320], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+352], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+384], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+416], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+448], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+480], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+512], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+544], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+576], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+608], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+640], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+672], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+704], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+736], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+768], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+40]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+72]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+104]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+136]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+168]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+200]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+232]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+264]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+296]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+328]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+360]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+392]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+424]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+456]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+488]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+520]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+552]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+584]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+616]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+648]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+680]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+712]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+744]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+776]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+40], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+72], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+104], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+136], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+168], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+200], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+232], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+264], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+296], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+328], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+360], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+392], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+424], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+456], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+488], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+520], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+552], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+584], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+616], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+648], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+680], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+712], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+744], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+776], rax
	mov rax, QWORD PTR [r8+16]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+48]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+80]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+112]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+144]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+176]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+208]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+240]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+272]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+304]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+336]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+368]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+400]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+432]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+464]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+496]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+528]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+560]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+592]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+624]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+656]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+688]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+720]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+752]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+784]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+16], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+48], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+80], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+112], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+144], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+176], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+208], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+240], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+272], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+304], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+336], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+368], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+400], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+432], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+464], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+496], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+528], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+560], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+592], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+624], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+656], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+688], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+720], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+752], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+784], rax
	mov rax, QWORD PTR [r8+24]
	mov QWORD PTR [r8+800], rax
	mov rax, QWORD PTR [r8+56]
	mov QWORD PTR [r8+808], rax
	mov rax, QWORD PTR [r8+88]
	mov QWORD PTR [r8+816], rax
	mov rax, QWORD PTR [r8+120]
	mov QWORD PTR [r8+824], rax
	mov rax, QWORD PTR [r8+152]
	mov QWORD PTR [r8+832], rax
	mov rax, QWORD PTR [r8+184]
	mov QWORD PTR [r8+840], rax
	mov rax, QWORD PTR [r8+216]
	mov QWORD PTR [r8+848], rax
	mov rax, QWORD PTR [r8+248]
	mov QWORD PTR [r8+856], rax
	mov rax, QWORD PTR [r8+280]
	mov QWORD PTR [r8+864], rax
	mov rax, QWORD PTR [r8+312]
	mov QWORD PTR [r8+872], rax
	mov rax, QWORD PTR [r8+344]
	mov QWORD PTR [r8+880], rax
	mov rax, QWORD PTR [r8+376]
	mov QWORD PTR [r8+888], rax
	mov rax, QWORD PTR [r8+408]
	mov QWORD PTR [r8+896], rax
	mov rax, QWORD PTR [r8+440]
	mov QWORD PTR [r8+904], rax
	mov rax, QWORD PTR [r8+472]
	mov QWORD PTR [r8+912], rax
	mov rax, QWORD PTR [r8+504]
	mov QWORD PTR [r8+920], rax
	mov rax, QWORD PTR [r8+536]
	mov QWORD PTR [r8+928], rax
	mov rax, QWORD PTR [r8+568]
	mov QWORD PTR [r8+936], rax
	mov rax, QWORD PTR [r8+600]
	mov QWORD PTR [r8+944], rax
	mov rax, QWORD PTR [r8+632]
	mov QWORD PTR [r8+952], rax
	mov rax, QWORD PTR [r8+664]
	mov QWORD PTR [r8+960], rax
	mov rax, QWORD PTR [r8+696]
	mov QWORD PTR [r8+968], rax
	mov rax, QWORD PTR [r8+728]
	mov QWORD PTR [r8+976], rax
	mov rax, QWORD PTR [r8+760]
	mov QWORD PTR [r8+984], rax
	mov rax, QWORD PTR [r8+792]
	mov QWORD PTR [r8+992], rax
	mov rdi, r8
	add rdi, 800
	mov rsi, r8
	add rsi, 1000
	call {vg_keccak_f1600}
	mov r8, rdi
	sub r8, 800
	mov rax, QWORD PTR [r8+800]
	mov QWORD PTR [r8+24], rax
	mov rax, QWORD PTR [r8+808]
	mov QWORD PTR [r8+56], rax
	mov rax, QWORD PTR [r8+816]
	mov QWORD PTR [r8+88], rax
	mov rax, QWORD PTR [r8+824]
	mov QWORD PTR [r8+120], rax
	mov rax, QWORD PTR [r8+832]
	mov QWORD PTR [r8+152], rax
	mov rax, QWORD PTR [r8+840]
	mov QWORD PTR [r8+184], rax
	mov rax, QWORD PTR [r8+848]
	mov QWORD PTR [r8+216], rax
	mov rax, QWORD PTR [r8+856]
	mov QWORD PTR [r8+248], rax
	mov rax, QWORD PTR [r8+864]
	mov QWORD PTR [r8+280], rax
	mov rax, QWORD PTR [r8+872]
	mov QWORD PTR [r8+312], rax
	mov rax, QWORD PTR [r8+880]
	mov QWORD PTR [r8+344], rax
	mov rax, QWORD PTR [r8+888]
	mov QWORD PTR [r8+376], rax
	mov rax, QWORD PTR [r8+896]
	mov QWORD PTR [r8+408], rax
	mov rax, QWORD PTR [r8+904]
	mov QWORD PTR [r8+440], rax
	mov rax, QWORD PTR [r8+912]
	mov QWORD PTR [r8+472], rax
	mov rax, QWORD PTR [r8+920]
	mov QWORD PTR [r8+504], rax
	mov rax, QWORD PTR [r8+928]
	mov QWORD PTR [r8+536], rax
	mov rax, QWORD PTR [r8+936]
	mov QWORD PTR [r8+568], rax
	mov rax, QWORD PTR [r8+944]
	mov QWORD PTR [r8+600], rax
	mov rax, QWORD PTR [r8+952]
	mov QWORD PTR [r8+632], rax
	mov rax, QWORD PTR [r8+960]
	mov QWORD PTR [r8+664], rax
	mov rax, QWORD PTR [r8+968]
	mov QWORD PTR [r8+696], rax
	mov rax, QWORD PTR [r8+976]
	mov QWORD PTR [r8+728], rax
	mov rax, QWORD PTR [r8+984]
	mov QWORD PTR [r8+760], rax
	mov rax, QWORD PTR [r8+992]
	mov QWORD PTR [r8+792], rax
	movq r9, xmm8
	movq r10, xmm9
	movq r11, xmm10
	movq rax, xmm11
	mov QWORD PTR [r8+2368], rax
	movq rax, xmm12
	mov QWORD PTR [r8+2376], rax
	movq rax, xmm13
	mov QWORD PTR [r8+2384], rax
	mov rdi, QWORD PTR [r8+2368]
	mov rdx, QWORD PTR [r8+2376]
	mov rsi, QWORD PTR [r8+2384]
	mov ecx, 0
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [r8+32]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [r8+64]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [r8+40]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r8+72]
	mov QWORD PTR [r9+72], rax
	mov rax, QWORD PTR [r8+16]
	mov QWORD PTR [r10+56], rax
	mov rax, QWORD PTR [r8+48]
	mov QWORD PTR [r10+64], rax
	mov rax, QWORD PTR [r8+80]
	mov QWORD PTR [r10+72], rax
	mov rax, QWORD PTR [r8+24]
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [r8+56]
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [r8+88]
	mov QWORD PTR [r11+72], rax
	ret
	.p2align 6
