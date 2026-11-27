// The functions of `src/internal/vg_cast5_lookup_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_lookup_ssse3:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_SSSE3}
	pop ecx
	mov edx, eax
	movdqu xmm2, XMMWORD PTR [edx+4384]
	pshufb xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [edx+4368]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm2
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [edx+4096]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [esi+272], xmm2
	movdqu xmm3, XMMWORD PTR [edx+4112]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [esi+288], xmm3
	movdqu xmm4, XMMWORD PTR [edx+4128]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [esi+304], xmm4
	movdqu xmm5, XMMWORD PTR [edx+4144]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [esi+320], xmm5
	movdqu xmm6, XMMWORD PTR [edx+4160]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [esi+336], xmm6
	movdqu xmm7, XMMWORD PTR [edx+4176]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [esi+352], xmm7
	movdqu xmm2, XMMWORD PTR [edx+4192]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [esi+368], xmm2
	movdqu xmm3, XMMWORD PTR [edx+4208]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [esi+384], xmm3
	movdqu xmm4, XMMWORD PTR [edx+4224]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [esi+400], xmm4
	movdqu xmm5, XMMWORD PTR [edx+4240]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [esi+416], xmm5
	movdqu xmm6, XMMWORD PTR [edx+4256]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [esi+432], xmm6
	movdqu xmm7, XMMWORD PTR [edx+4272]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [esi+448], xmm7
	movdqu xmm2, XMMWORD PTR [edx+4288]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [esi+464], xmm2
	movdqu xmm3, XMMWORD PTR [edx+4304]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [esi+480], xmm3
	movdqu xmm4, XMMWORD PTR [edx+4320]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [esi+496], xmm4
	movdqu xmm5, XMMWORD PTR [edx+4336]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [esi+512], xmm5
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+256]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+512]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+768]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+16]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+272]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+528]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+784]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+32]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+288]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+544]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+800]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+48]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+304]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+560]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+816]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+64]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+320]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+576]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+832]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+80]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+336]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+592]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+848]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+96]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+352]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+608]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+864]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+112]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+368]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+624]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+880]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+128]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+384]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+640]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+896]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+144]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+400]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+656]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+912]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+160]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+416]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+672]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+928]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+176]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+432]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+688]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+944]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+192]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+448]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+704]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+960]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+208]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+464]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+720]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+976]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+224]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+480]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+736]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+992]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+240]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+496]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+752]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1008]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	punpckldq xmm4, xmm5
	punpckldq xmm6, xmm7
	punpcklqdq xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm0
	movdqu XMMWORD PTR [esi+528], xmm4
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+1024]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+1280]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+1536]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+1792]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1296]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1552]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1808]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+1056]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+1312]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+1568]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+1072]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1328]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+1584]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+1840]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+1088]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1600]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1856]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+1104]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+1360]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+1616]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+1872]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+1120]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1376]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1632]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+1888]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+1136]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+1392]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1904]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+1152]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+1408]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+1664]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+1920]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1424]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1680]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1936]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+1184]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+1440]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+1696]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+1200]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1456]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+1712]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+1968]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+1216]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+1728]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1984]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+1232]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+1488]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+1744]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2000]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+1248]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+1504]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+1760]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+2016]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+1264]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+1520]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2032]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	punpckldq xmm4, xmm5
	punpckldq xmm6, xmm7
	punpcklqdq xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm0
	movdqu XMMWORD PTR [esi+544], xmm4
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+2048]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+2304]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+2560]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+2816]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2320]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+2576]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2832]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+2080]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+2336]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2592]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+2096]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2352]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+2608]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+2864]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+2112]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2624]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+2880]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+2128]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+2384]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+2640]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2896]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+2144]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+2400]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2656]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+2912]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+2160]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2416]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2928]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+2176]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+2432]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+2688]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+2944]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2448]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+2704]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2960]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+2208]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+2464]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2720]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+2224]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2480]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+2736]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+2992]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+2240]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+2752]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3008]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+2256]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+2512]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+2768]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3024]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+2272]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+2528]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+2784]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+3040]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+2288]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+2544]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3056]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	punpckldq xmm4, xmm5
	punpckldq xmm6, xmm7
	punpcklqdq xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm0
	movdqu XMMWORD PTR [esi+560], xmm4
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+3072]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+3328]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+3584]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+3840]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+3088]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3344]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3600]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3856]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+3104]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+3360]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3616]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+3872]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+3120]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3376]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+3632]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+3888]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+3136]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3648]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3904]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+3152]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+3408]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+3664]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3920]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+3168]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3424]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3680]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+3936]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+3184]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3440]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+3696]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3952]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+3200]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+3456]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+3712]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+3968]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+3216]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3472]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3728]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3984]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+3232]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+3488]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3744]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+3248]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3504]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+3760]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+4016]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+3264]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+3776]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+4032]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+3280]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+3536]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+3792]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+4048]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+3296]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+3552]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+3808]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+4064]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+3312]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+3568]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+4080]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	punpckldq xmm4, xmm5
	punpckldq xmm6, xmm7
	punpcklqdq xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm0
	movdqu XMMWORD PTR [esi+576], xmm4
	movdqu xmm1, XMMWORD PTR [esi+576]
	movdqu xmm2, XMMWORD PTR [esi+560]
	punpckldq xmm1, xmm2
	pshufd xmm1, xmm1, 12
	movdqu xmm3, XMMWORD PTR [esi+544]
	movdqu xmm2, XMMWORD PTR [esi+528]
	punpckhdq xmm3, xmm2
	pshufd xmm3, xmm3, 12
	punpcklqdq xmm1, xmm3
	ret
	.p2align 6
