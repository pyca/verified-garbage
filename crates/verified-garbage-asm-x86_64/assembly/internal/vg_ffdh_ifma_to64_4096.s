// The functions of `src/internal/vg_ffdh_ifma_to64_4096.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_ifma_to64_4096:
	mov r11, QWORD PTR [rdi+232]
	add r11, 672
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+256]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+256]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+288]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+288]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+320]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+352]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+352]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+384]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+384]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+416]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+416]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+448]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+448]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+480]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+512]
	or rax, rcx
	mov rcx, QWORD PTR [r11+544]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+544]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+576]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+576]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+608]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+608]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+328]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+328]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+360]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+392]
	or rax, rcx
	mov rcx, QWORD PTR [r11+424]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+424]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+456]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+456]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+488]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+488]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+520]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+520]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+552]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+584]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+584]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+616]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+616]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+256], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+264], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+272], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+280], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+288], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+296], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+304], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+312], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+336]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+320], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+336]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+368]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+328], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+368]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+400]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+336], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+400]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+432]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+464]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+344], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+464]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+496]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+352], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+496]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+528]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+360], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+528]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+560]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+368], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+560]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+592]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+624]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+376], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+624]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+384], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+392], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+400], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+408], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+416], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+424], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+432], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+248]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+440], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+344]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+448], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+344]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+376]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+456], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+376]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+408]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+464], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+408]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+440]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+472], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+440]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+472]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+504]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+480], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+504]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+536]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+488], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+536]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+568]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+496], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+568]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+600]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+504], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+600]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+632]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+512], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	ret
	.p2align 6
