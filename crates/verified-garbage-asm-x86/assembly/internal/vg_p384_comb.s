// The functions of `src/internal/vg_p384_comb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_comb:
	mov eax, -675051162
	mov DWORD PTR [edi+1984], eax
	mov eax, 406100306
	mov DWORD PTR [edi+1988], eax
	mov eax, 1860475076
	mov DWORD PTR [edi+1992], eax
	mov eax, -444790389
	mov DWORD PTR [edi+1996], eax
	mov eax, 1264584334
	mov DWORD PTR [edi+2000], eax
	mov eax, 1742102993
	mov DWORD PTR [edi+2004], eax
	mov eax, -1111842649
	mov DWORD PTR [edi+2008], eax
	mov eax, -1448746037
	mov DWORD PTR [edi+2012], eax
	mov eax, 1560699326
	mov DWORD PTR [edi+2016], eax
	mov eax, 578905564
	mov DWORD PTR [edi+2020], eax
	mov eax, 552550381
	mov DWORD PTR [edi+2024], eax
	mov eax, 1729639394
	mov DWORD PTR [edi+2028], eax
	mov eax, -265822636
	mov DWORD PTR [edi+736], eax
	mov eax, -1343843027
	mov DWORD PTR [edi+740], eax
	mov eax, -2034856783
	mov DWORD PTR [edi+744], eax
	mov eax, 1548552743
	mov DWORD PTR [edi+748], eax
	mov eax, 1677781025
	mov DWORD PTR [edi+752], eax
	mov eax, 1838641271
	mov DWORD PTR [edi+756], eax
	mov eax, 1270887808
	mov DWORD PTR [edi+760], eax
	mov eax, 1117556599
	mov DWORD PTR [edi+764], eax
	mov eax, -1753488167
	mov DWORD PTR [edi+768], eax
	mov eax, -987129852
	mov DWORD PTR [edi+772], eax
	mov eax, 1363739878
	mov DWORD PTR [edi+776], eax
	mov eax, -623235581
	mov DWORD PTR [edi+780], eax
	mov eax, 1798755256
	mov DWORD PTR [edi+784], eax
	mov eax, 1205005364
	mov DWORD PTR [edi+788], eax
	mov eax, -1937993583
	mov DWORD PTR [edi+792], eax
	mov eax, 89348122
	mov DWORD PTR [edi+796], eax
	mov eax, 1735881151
	mov DWORD PTR [edi+800], eax
	mov eax, -1138332088
	mov DWORD PTR [edi+804], eax
	mov eax, -2111842857
	mov DWORD PTR [edi+808], eax
	mov eax, 937387158
	mov DWORD PTR [edi+812], eax
	mov eax, 1487927515
	mov DWORD PTR [edi+816], eax
	mov eax, 649849653
	mov DWORD PTR [edi+820], eax
	mov eax, 1250010626
	mov DWORD PTR [edi+824], eax
	mov eax, -734946292
	mov DWORD PTR [edi+828], eax
	mov eax, 1
	mov DWORD PTR [edi+832], eax
	mov eax, -1
	mov DWORD PTR [edi+836], eax
	mov eax, -1
	mov DWORD PTR [edi+840], eax
	mov eax, 0
	mov DWORD PTR [edi+844], eax
	mov eax, 1
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov DWORD PTR [edi+860], eax
	mov eax, 0
	mov DWORD PTR [edi+864], eax
	mov eax, 0
	mov DWORD PTR [edi+868], eax
	mov eax, 0
	mov DWORD PTR [edi+872], eax
	mov eax, 0
	mov DWORD PTR [edi+876], eax
	mov esi, 55
20:
	sub esi, 1
	cmp esi, 54
	je 21f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4102]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4101]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4100]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	jmp 22f
21:
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4101]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4100]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
22:
	mov eax, esi
	mov ecx, 6144
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 19
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1968]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2304]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2320]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2336]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2352]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2560]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2576]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2592]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2608]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2688]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2704]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2720]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2736]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2928]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3072]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3088]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3104]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3120]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3200]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3216]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3232]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3248]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3264]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3280]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3296]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3312]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3328]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3344]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3360]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3376]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3456]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3472]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3488]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3504]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3536]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3552]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3568]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3584]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3600]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3616]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3632]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3648]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3664]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3680]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3696]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3712]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3728]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3744]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3760]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3840]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3856]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3872]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3888]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3904]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3968]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3984]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4016]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4032]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4048]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4064]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4080]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4096]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4112]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4128]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4144]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4160]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4176]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4192]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4208]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4240]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4256]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4272]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4288]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4304]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4368]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4384]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4400]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4416]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4432]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4448]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4464]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4480]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4496]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4512]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4528]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4544]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4560]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4576]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4592]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4608]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4624]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4640]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4656]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4672]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4688]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4704]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4720]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4736]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4752]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4768]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4784]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4800]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4816]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4832]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4848]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4864]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4880]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4896]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4912]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4928]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4944]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4960]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4976]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4992]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5008]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5024]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5040]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5056]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5072]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5088]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5104]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5120]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5136]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5152]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5168]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5184]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5200]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5216]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5232]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5248]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5264]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5312]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5328]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5344]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5360]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5376]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5392]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5408]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5424]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5440]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5456]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5472]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5488]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5504]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5520]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5536]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5552]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5568]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5584]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5600]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5616]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5632]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5648]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5664]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5680]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5696]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5712]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5728]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5744]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5776]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5792]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5808]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5824]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5840]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5856]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5872]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5888]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5904]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5920]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5936]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5952]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5968]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5984]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6000]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6016]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6032]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6048]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6064]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6080]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6096]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6112]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6128]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+1024], xmm0
	movdqu XMMWORD PTR [edi+1040], xmm1
	movdqu XMMWORD PTR [edi+1056], xmm2
	movdqu XMMWORD PTR [edi+1072], xmm3
	movdqu XMMWORD PTR [edi+1088], xmm4
	movdqu XMMWORD PTR [edi+1104], xmm5
	mov eax, 1
	mov DWORD PTR [edi+1120], eax
	mov eax, -1
	mov DWORD PTR [edi+1124], eax
	mov eax, -1
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	mov DWORD PTR [edi+1132], eax
	mov eax, 1
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov eax, 0
	mov DWORD PTR [edi+1152], eax
	mov eax, 0
	mov DWORD PTR [edi+1156], eax
	mov eax, 0
	mov DWORD PTR [edi+1160], eax
	mov eax, 0
	mov DWORD PTR [edi+1164], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+1072]
	mov edx, DWORD PTR [edi+1120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	mov edx, DWORD PTR [edi+1124]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	mov edx, DWORD PTR [edi+1128]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	mov edx, DWORD PTR [edi+1132]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1088]
	mov edx, DWORD PTR [edi+1136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	mov edx, DWORD PTR [edi+1140]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	mov edx, DWORD PTR [edi+1144]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	mov edx, DWORD PTR [edi+1148]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1104]
	mov edx, DWORD PTR [edi+1152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	mov edx, DWORD PTR [edi+1156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	mov edx, DWORD PTR [edi+1160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	mov edx, DWORD PTR [edi+1164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1120]
	mov edx, DWORD PTR [edi+208]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1124]
	mov edx, DWORD PTR [edi+212]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1128]
	mov edx, DWORD PTR [edi+216]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1132]
	mov edx, DWORD PTR [edi+220]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1136]
	mov edx, DWORD PTR [edi+224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1140]
	mov edx, DWORD PTR [edi+228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1144]
	mov edx, DWORD PTR [edi+232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1148]
	mov edx, DWORD PTR [edi+236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1152]
	mov edx, DWORD PTR [edi+240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1156]
	mov edx, DWORD PTR [edi+244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1160]
	mov edx, DWORD PTR [edi+248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1164]
	mov edx, DWORD PTR [edi+252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1164], eax
	mov eax, 1072
	mov ecx, 208
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 54
	je 23f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 24f
23:
	mov ecx, -1
24:
	mov eax, DWORD PTR [edi+1072]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1088]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1104]
	mov edx, DWORD PTR [edi+1536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	mov edx, DWORD PTR [edi+1540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	mov edx, DWORD PTR [edi+1544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	mov edx, DWORD PTR [edi+1548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, 1024
	mov ecx, 736
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1072
	mov ecx, 784
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 832
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 736
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1072
	mov ecx, 1024
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1168
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 736
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1024
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 784
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1072
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 352
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1984
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1168
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1984
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1216
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1408
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1312
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 880
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1312
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1408
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 976
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+944]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+948]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+952]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+956]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+876], eax
	test esi, esi
	jne 20b
	ret
	.p2align 6
