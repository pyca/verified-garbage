// The functions of `src/internal/vg_brainpoolp512r1_comb_g.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_comb_g:
	movabs rax, 5800218050920262196
	mov QWORD PTR [rdi+2624], rax
	movabs rax, 43738331591105076
	mov QWORD PTR [rdi+2632], rax
	movabs rax, -2203486902629751638
	mov QWORD PTR [rdi+2640], rax
	movabs rax, -4089777636057301502
	mov QWORD PTR [rdi+2648], rax
	movabs rax, -7502983355594300365
	mov QWORD PTR [rdi+2656], rax
	movabs rax, -3757594541010986979
	mov QWORD PTR [rdi+2664], rax
	movabs rax, 7215631528053025442
	mov QWORD PTR [rdi+2672], rax
	movabs rax, 7659122907072597671
	mov QWORD PTR [rdi+2680], rax
	movabs rax, 2849205283292668077
	mov QWORD PTR [rdi+960], rax
	movabs rax, -552263363139552676
	mov QWORD PTR [rdi+968], rax
	movabs rax, 2759677414701170351
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1183303483114238159
	mov QWORD PTR [rdi+984], rax
	movabs rax, 6027767431898983111
	mov QWORD PTR [rdi+992], rax
	movabs rax, -2322611779757094726
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 8818932739302589296
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 6638648451672006787
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 2188231064055216604
	mov QWORD PTR [rdi+1024], rax
	movabs rax, 6432439057298086477
	mov QWORD PTR [rdi+1032], rax
	movabs rax, 2640470948666540620
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -8147572589399520562
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1881910245790592535
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 7335503105966509061
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 8526652370706143589
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 6065117409837853105
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -2930260431521597683
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -2918894611604883078
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 5850843135254232857
	mov QWORD PTR [rdi+1104], rax
	movabs rax, -9029043254863489091
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 2998380533618898830
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 3805385882173058545
	mov QWORD PTR [rdi+1128], rax
	movabs rax, -4599554755319692296
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 6134573700119673716
	mov QWORD PTR [rdi+1144], rax
	mov eax, 0
	mov QWORD PTR [rdi+3456], rax
	mov ebx, 74
20:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2950]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2949]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2948]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2947]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2946]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2945]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2944]
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
	mov ecx, 8192
	mul rcx
	lea rdx, {VG_BRAINPOOLP512R1_COMB}
	add rdx, rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
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
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+288]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+304]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+320]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+336]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+352]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+368]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 4
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
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+640]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+656]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 7
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
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 9
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 10
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
	movdqu xmm14, XMMWORD PTR [rdx+1248]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1264]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 11
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1504]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1520]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 13
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
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1728]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1744]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1760]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1776]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 15
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1792]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1808]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 16
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
	movdqu xmm14, XMMWORD PTR [rdx+2016]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2032]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 17
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2048]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2064]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2080]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2096]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 18
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 19
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
	movdqu xmm14, XMMWORD PTR [rdx+2400]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2416]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 20
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 21
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2560]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2576]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2592]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2608]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2624]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2640]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2656]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2672]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 22
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
	movdqu xmm14, XMMWORD PTR [rdx+2784]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2800]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 23
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2816]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2832]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2848]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2864]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2880]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2896]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2912]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2928]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 24
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2944]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2960]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2976]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2992]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3008]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3024]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3040]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3056]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 25
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
	movdqu xmm14, XMMWORD PTR [rdx+3168]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3184]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 26
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3200]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3216]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3232]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3248]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3264]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3280]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3296]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3312]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 27
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3328]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3344]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3360]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3376]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3392]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3408]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3424]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3440]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 28
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
	movdqu xmm14, XMMWORD PTR [rdx+3552]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3568]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 29
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3584]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3600]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3616]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3632]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3648]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3664]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3680]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3696]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 30
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3712]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3728]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3744]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3760]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3776]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3792]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3808]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3824]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 31
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
	movdqu xmm14, XMMWORD PTR [rdx+3936]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3952]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 32
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3968]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3984]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4000]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4016]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4032]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4048]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4064]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4080]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 33
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4096]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4112]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4128]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4144]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4160]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4176]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4192]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4208]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 34
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
	movdqu xmm14, XMMWORD PTR [rdx+4320]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4336]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 35
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4352]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4368]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4384]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4400]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4416]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4432]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4448]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4464]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 36
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4480]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4496]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4512]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4528]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4544]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4560]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4576]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4592]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 37
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
	movdqu xmm14, XMMWORD PTR [rdx+4704]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4720]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 38
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4736]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4752]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4768]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4784]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4800]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4816]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4832]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4848]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 39
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4976]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 40
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
	movdqu xmm14, XMMWORD PTR [rdx+5088]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5104]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 41
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5120]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5136]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5152]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5168]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5184]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5200]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5216]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5232]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 42
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5248]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5264]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5280]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5296]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5312]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5328]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5344]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5360]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 43
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
	movdqu xmm14, XMMWORD PTR [rdx+5472]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5488]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 44
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5504]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5520]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5536]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5552]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5568]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5584]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5600]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5616]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 45
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5632]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5648]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5664]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5680]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5696]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5712]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5728]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5744]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 46
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
	movdqu xmm14, XMMWORD PTR [rdx+5856]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5872]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 47
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5888]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5904]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5920]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5936]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5952]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5968]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5984]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6000]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 48
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6016]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6032]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6048]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6064]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6080]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6096]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6112]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6128]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 49
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6144]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6160]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6176]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6192]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6208]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6224]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6240]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6256]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 50
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6272]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6288]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6304]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6320]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6336]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6352]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6368]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6384]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 51
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6400]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6416]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6432]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6448]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6464]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6480]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6496]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6512]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 52
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6528]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6544]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6560]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6576]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6592]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6608]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6624]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6640]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 53
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6656]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6672]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6688]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6704]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6720]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6736]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6752]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6768]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 54
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6784]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6800]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6816]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6832]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6848]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6864]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6880]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6896]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 55
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6912]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6928]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6944]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6960]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6976]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6992]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7008]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7024]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 56
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7040]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7056]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7072]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7088]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7104]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7120]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7136]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7152]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 57
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7168]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7184]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7200]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7216]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7232]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7248]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7264]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7280]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 58
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7408]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 59
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7424]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7440]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7456]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7472]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7488]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7504]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7520]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7536]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 60
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7552]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7568]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7584]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7600]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7616]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7632]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7648]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7664]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 61
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7680]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7696]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7712]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7728]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7744]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7760]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7776]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7792]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 62
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7808]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7824]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7840]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7856]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7872]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7888]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7904]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7920]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 63
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7936]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7952]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7968]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7984]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8000]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8016]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8032]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8048]
	pand xmm14, xmm15
	por xmm7, xmm14
	mov ecx, 64
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8064]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8080]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8096]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8112]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8128]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8144]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8160]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8176]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu XMMWORD PTR [rdi+1344], xmm0
	movdqu XMMWORD PTR [rdi+1360], xmm1
	movdqu XMMWORD PTR [rdi+1376], xmm2
	movdqu XMMWORD PTR [rdi+1392], xmm3
	movdqu XMMWORD PTR [rdi+1408], xmm4
	movdqu XMMWORD PTR [rdi+1424], xmm5
	movdqu XMMWORD PTR [rdi+1440], xmm6
	movdqu XMMWORD PTR [rdi+1456], xmm7
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, -2930260431521597683
	and rax, rcx
	or rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1408], rax
	movabs rax, -2918894611604883078
	and rax, rcx
	or rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 5850843135254232857
	and rax, rcx
	or rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1424], rax
	movabs rax, -9029043254863489091
	and rax, rcx
	or rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 2998380533618898830
	and rax, rcx
	or rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 3805385882173058545
	and rax, rcx
	or rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1448], rax
	movabs rax, -4599554755319692296
	and rax, rcx
	or rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 6134573700119673716
	and rax, rcx
	or rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1464], rax
	xor rcx, -1
	movabs rax, -2930260431521597683
	and rax, rcx
	mov QWORD PTR [rdi+1472], rax
	movabs rax, -2918894611604883078
	and rax, rcx
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 5850843135254232857
	and rax, rcx
	mov QWORD PTR [rdi+1488], rax
	movabs rax, -9029043254863489091
	and rax, rcx
	mov QWORD PTR [rdi+1496], rax
	movabs rax, 2998380533618898830
	and rax, rcx
	mov QWORD PTR [rdi+1504], rax
	movabs rax, 3805385882173058545
	and rax, rcx
	mov QWORD PTR [rdi+1512], rax
	movabs rax, -4599554755319692296
	and rax, rcx
	mov QWORD PTR [rdi+1520], rax
	movabs rax, 6134573700119673716
	and rax, rcx
	mov QWORD PTR [rdi+1528], rax
	mov r8, QWORD PTR [rdi+256]
	sub r8, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+264]
	sbb r8, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+272]
	sbb r8, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+280]
	sbb r8, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+288]
	sbb r8, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+296]
	sbb r8, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+304]
	sbb r8, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+312]
	sbb r8, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+1984], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+1992], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+2000], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+2008], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+2016], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+2024], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+2032], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+2040], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+1984]
	mov QWORD PTR [rdi+1984], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+1992]
	mov QWORD PTR [rdi+1992], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+2000]
	mov QWORD PTR [rdi+2000], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+2008]
	mov QWORD PTR [rdi+2008], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+2016]
	mov QWORD PTR [rdi+2016], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+2024]
	mov QWORD PTR [rdi+2024], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+2032]
	mov QWORD PTR [rdi+2032], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+2040]
	mov QWORD PTR [rdi+2040], r8
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2950]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1984]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1992]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+2000]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+2008]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+2016]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+2024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+2032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+2040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1464], rax
	movabs rax, -3976350352470362711
	mov QWORD PTR [rdi+1984], rax
	movabs rax, -2787679616831567849
	mov QWORD PTR [rdi+1992], rax
	movabs rax, -759617572635022057
	mov QWORD PTR [rdi+2000], rax
	movabs rax, -2851632089325841979
	mov QWORD PTR [rdi+2008], rax
	movabs rax, -1063825459454450647
	mov QWORD PTR [rdi+2016], rax
	movabs rax, -7467397740859902391
	mov QWORD PTR [rdi+2024], rax
	movabs rax, -1399404244870167584
	mov QWORD PTR [rdi+2032], rax
	movabs rax, -7781545726081636502
	mov QWORD PTR [rdi+2040], rax
	call {vg_brainpoolp512r1_add_complete}
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2950]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2949]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2948]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2947]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2946]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2945]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2944]
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
	mov rax, QWORD PTR [rdi+1152]
	mov rdx, QWORD PTR [rdi+960]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rdi+1160]
	mov rdx, QWORD PTR [rdi+968]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rdi+1168]
	mov rdx, QWORD PTR [rdi+976]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rdi+1176]
	mov rdx, QWORD PTR [rdi+984]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rdi+1184]
	mov rdx, QWORD PTR [rdi+992]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1192]
	mov rdx, QWORD PTR [rdi+1000]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1200]
	mov rdx, QWORD PTR [rdi+1008]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1208]
	mov rdx, QWORD PTR [rdi+1016]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	mov rax, QWORD PTR [rdi+1216]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1024], rax
	mov rax, QWORD PTR [rdi+1224]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1032], rax
	mov rax, QWORD PTR [rdi+1232]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1040], rax
	mov rax, QWORD PTR [rdi+1240]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1048], rax
	mov rax, QWORD PTR [rdi+1248]
	mov rdx, QWORD PTR [rdi+1056]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1256]
	mov rdx, QWORD PTR [rdi+1064]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1264]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1272]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1280]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	test rbx, rbx
	jne 20b
	ret
	.p2align 6
