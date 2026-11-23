// The functions of `src/internal/vg_p521_mul_base.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_base:
	mov QWORD PTR [rdi+2152], rbx
	mov QWORD PTR [rdi+2160], rbp
	mov QWORD PTR [rdi+2168], r12
	mov QWORD PTR [rdi+2176], r13
	mov QWORD PTR [rdi+2184], r14
	mov QWORD PTR [rdi+2192], r15
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	movabs rax, -2911398454546468714
	mov QWORD PTR [rdi+1072], rax
	movabs rax, -2622805883304785837
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -6758855595800436770
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -3350014429734814130
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 9185203175476711091
	mov QWORD PTR [rdi+1104], rax
	movabs rax, -2793569313455226504
	mov QWORD PTR [rdi+1112], rax
	movabs rax, -9062608006907465467
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 3497699202216198480
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 458
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 5408250952697325544
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -267932407593670216
	mov QWORD PTR [rdi+1152], rax
	movabs rax, -8885807591840917390
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 8614545525818659092
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 4212919814057000474
	mov QWORD PTR [rdi+1176], rax
	movabs rax, -7381687526187518677
	mov QWORD PTR [rdi+1184], rax
	movabs rax, -4256878057158064348
	mov QWORD PTR [rdi+1192], rax
	movabs rax, -2260134842321433193
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 209
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov eax, 0
	mov QWORD PTR [rdi+3880], rax
	mov ebx, 83
21:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
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
	mov ecx, 9216
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
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
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 3
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
	movdqu xmm14, XMMWORD PTR [rdx+384]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+400]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 5
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
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+768]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+784]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+800]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+816]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+832]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 7
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
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 9
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
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 10
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 11
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
	movdqu xmm14, XMMWORD PTR [rdx+1536]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1552]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1568]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1584]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1600]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1616]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 13
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
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1920]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1936]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1952]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1968]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1984]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2000]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 15
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
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 16
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 17
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
	movdqu xmm14, XMMWORD PTR [rdx+2432]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 18
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2448]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2464]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2480]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2560]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2576]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 19
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
	movdqu xmm14, XMMWORD PTR [rdx+2688]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2704]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2720]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 20
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2736]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2752]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2768]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2784]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2800]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2816]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2832]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2848]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2864]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 21
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
	movdqu xmm14, XMMWORD PTR [rdx+2976]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2992]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3008]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 22
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3024]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3040]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3056]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3072]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3088]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3104]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3120]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3136]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3152]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 23
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
	movdqu xmm14, XMMWORD PTR [rdx+3264]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3280]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3296]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 24
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3312]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3328]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3344]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3360]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3376]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3392]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3408]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3424]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3440]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 25
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
	movdqu xmm14, XMMWORD PTR [rdx+3584]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 26
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3600]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3616]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3632]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3648]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3664]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3680]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3696]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3712]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3728]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 27
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
	movdqu xmm14, XMMWORD PTR [rdx+3840]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3856]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3872]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 28
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3888]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3904]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3920]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3936]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3952]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3968]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3984]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4000]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4016]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 29
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
	movdqu xmm14, XMMWORD PTR [rdx+4128]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4144]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4160]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 30
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4176]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4192]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4208]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4224]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4240]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4256]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4272]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4288]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4304]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 31
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
	movdqu xmm14, XMMWORD PTR [rdx+4416]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4432]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4448]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 32
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4464]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4480]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4496]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4512]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4528]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4544]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4560]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4576]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4592]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 33
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
	movdqu xmm14, XMMWORD PTR [rdx+4736]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 34
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4752]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4768]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4784]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4800]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4816]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4832]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4848]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4864]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4880]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 35
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
	movdqu xmm14, XMMWORD PTR [rdx+4992]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5008]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5024]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 36
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5040]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5056]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5072]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5088]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5104]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5120]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5136]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5152]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5168]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 37
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
	movdqu xmm14, XMMWORD PTR [rdx+5280]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5296]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5312]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 38
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5328]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5344]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5360]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5376]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5392]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5408]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5424]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5440]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5456]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 39
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
	movdqu xmm14, XMMWORD PTR [rdx+5568]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5584]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5600]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 40
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5616]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5632]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5648]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5664]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5680]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5696]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5712]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5728]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5744]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 41
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
	movdqu xmm14, XMMWORD PTR [rdx+5888]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 42
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5904]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5920]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5936]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5952]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5968]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5984]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6000]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6016]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6032]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 43
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
	movdqu xmm14, XMMWORD PTR [rdx+6144]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6160]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6176]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 44
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6192]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6208]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6224]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6240]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6256]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6272]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6288]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6304]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6320]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 45
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6336]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6352]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6368]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6384]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6400]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6416]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6432]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6448]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6464]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 46
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6480]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6496]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6512]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6528]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6544]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6560]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6576]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6592]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6608]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 47
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6624]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6640]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6656]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6672]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6688]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6704]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6720]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6736]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6752]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 48
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6768]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6784]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6800]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6816]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6832]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6848]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6864]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6880]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6896]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 49
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
	movdqu xmm14, XMMWORD PTR [rdx+7040]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 50
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7056]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7072]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7088]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7104]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7120]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7136]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7152]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7168]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7184]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 51
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7200]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7216]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7232]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7248]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7264]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7280]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7296]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7312]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7328]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 52
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7344]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7360]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7376]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7392]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7408]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7424]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7440]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7456]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7472]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 53
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7488]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7504]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7520]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7536]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7552]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7568]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7584]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7600]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7616]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 54
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7632]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7648]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7664]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7680]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7696]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7712]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7728]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7744]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7760]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 55
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7776]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7792]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7808]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7824]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7840]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7856]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7872]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7888]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7904]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 56
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7920]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7936]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7952]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7968]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7984]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8000]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8016]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8032]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8048]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 57
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
	movdqu xmm14, XMMWORD PTR [rdx+8192]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 58
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8208]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8224]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8240]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8256]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8272]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8288]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8304]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8320]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8336]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 59
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8352]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8368]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8384]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8400]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8416]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8432]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8448]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8464]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8480]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 60
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8496]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8512]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8528]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8544]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8560]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8576]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8592]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8608]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8624]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 61
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8640]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8656]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8672]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8688]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8704]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8720]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8736]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8752]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8768]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 62
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8784]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8800]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8816]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8832]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8848]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8864]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8880]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8896]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8912]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 63
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8928]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8944]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8960]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8976]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8992]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9008]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9024]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9040]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9056]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 64
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+9072]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9088]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9104]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9120]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9136]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9152]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9168]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9184]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9200]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	xor rcx, -1
	movabs rax, 36028797018963968
	and rax, rcx
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+3310]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 2008
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1360
	mov edx, 1504
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -288
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 576
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
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
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	test rbx, rbx
	jne 21b
	mov rbx, QWORD PTR [rdi+2152]
	mov rbp, QWORD PTR [rdi+2160]
	mov r12, QWORD PTR [rdi+2168]
	mov r13, QWORD PTR [rdi+2176]
	mov r14, QWORD PTR [rdi+2184]
	mov r15, QWORD PTR [rdi+2192]
	ret
	.p2align 6
