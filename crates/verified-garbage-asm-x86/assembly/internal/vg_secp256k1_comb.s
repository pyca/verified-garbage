// The functions of `src/internal/vg_secp256k1_comb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_comb:
	mov eax, 20517
	mov DWORD PTR [edi+1344], eax
	mov eax, 21
	mov DWORD PTR [edi+1348], eax
	mov eax, 0
	mov DWORD PTR [edi+1352], eax
	mov eax, 0
	mov DWORD PTR [edi+1356], eax
	mov eax, 0
	mov DWORD PTR [edi+1360], eax
	mov eax, 0
	mov DWORD PTR [edi+1364], eax
	mov eax, 0
	mov DWORD PTR [edi+1368], eax
	mov eax, 0
	mov DWORD PTR [edi+1372], eax
	mov eax, -1770187162
	mov DWORD PTR [edi+512], eax
	mov eax, -799732372
	mov DWORD PTR [edi+516], eax
	mov eax, 1725741592
	mov DWORD PTR [edi+520], eax
	mov eax, 640167560
	mov DWORD PTR [edi+524], eax
	mov eax, 181310677
	mov DWORD PTR [edi+528], eax
	mov eax, 2127309687
	mov DWORD PTR [edi+532], eax
	mov eax, -859039942
	mov DWORD PTR [edi+536], eax
	mov eax, 1259106252
	mov DWORD PTR [edi+540], eax
	mov eax, -533045676
	mov DWORD PTR [edi+544], eax
	mov eax, 1958349141
	mov DWORD PTR [edi+548], eax
	mov eax, 1525739677
	mov DWORD PTR [edi+552], eax
	mov eax, 280646466
	mov DWORD PTR [edi+556], eax
	mov eax, 1355052081
	mov DWORD PTR [edi+560], eax
	mov eax, -2088546812
	mov DWORD PTR [edi+564], eax
	mov eax, 1863695636
	mov DWORD PTR [edi+568], eax
	mov eax, 946751079
	mov DWORD PTR [edi+572], eax
	mov eax, 977
	mov DWORD PTR [edi+576], eax
	mov eax, 1
	mov DWORD PTR [edi+580], eax
	mov eax, 0
	mov DWORD PTR [edi+584], eax
	mov eax, 0
	mov DWORD PTR [edi+588], eax
	mov eax, 0
	mov DWORD PTR [edi+592], eax
	mov eax, 0
	mov DWORD PTR [edi+596], eax
	mov eax, 0
	mov DWORD PTR [edi+600], eax
	mov eax, 0
	mov DWORD PTR [edi+604], eax
	mov esi, 37
20:
	sub esi, 1
	cmp esi, 36
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
	mov ecx, 4096
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
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
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 4
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
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 7
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
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 10
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
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 13
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
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 16
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
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 19
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
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 22
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
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 25
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
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 28
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
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 31
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
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 34
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
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 37
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
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 40
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
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2592]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2608]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 43
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
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 46
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
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 49
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
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3232]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3248]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 52
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
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3328]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3344]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3360]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3376]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 55
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
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3536]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3552]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3568]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3584]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3600]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3616]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3632]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 58
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
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3712]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3728]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3744]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3760]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 61
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
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3904]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3968]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3984]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4016]
	pand xmm6, xmm7
	por xmm3, xmm6
	mov ecx, 64
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
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm1
	movdqu XMMWORD PTR [edi+736], xmm2
	movdqu XMMWORD PTR [edi+752], xmm3
	mov eax, 977
	mov DWORD PTR [edi+768], eax
	mov eax, 1
	mov DWORD PTR [edi+772], eax
	mov eax, 0
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, 0
	mov DWORD PTR [edi+784], eax
	mov eax, 0
	mov DWORD PTR [edi+788], eax
	mov eax, 0
	mov DWORD PTR [edi+792], eax
	mov eax, 0
	mov DWORD PTR [edi+796], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+168]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+172]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+784]
	mov edx, DWORD PTR [edi+176]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+788]
	mov edx, DWORD PTR [edi+180]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+792]
	mov edx, DWORD PTR [edi+184]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+796]
	mov edx, DWORD PTR [edi+188]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+796], eax
	mov eax, 736
	mov ecx, 160
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 36
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
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, 704
	mov ecx, 512
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 544
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 576
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 512
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 704
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 512
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 704
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 544
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 256
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1344
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 1344
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 832
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 960
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 896
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 960
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	test esi, esi
	jne 20b
	ret
	.p2align 6
