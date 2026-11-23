// The functions of `src/internal/vg_cast5_key_lookup_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_key_lookup_ssse3:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_SSSE3}
	pop ecx
	mov edx, eax
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
	movdqu xmm1, XMMWORD PTR [edx+4480]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+4736]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+4992]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+5248]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+4496]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+4752]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5008]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5264]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+4512]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+4768]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+5024]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5280]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+4528]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+4784]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+5040]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+5296]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+4544]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+4800]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5056]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5312]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+4560]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+4816]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+5072]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+5328]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+4576]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+4832]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5088]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+5344]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+4592]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+4848]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5104]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5360]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+4608]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+4864]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+5120]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+5376]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+4624]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+4880]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5136]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5392]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+4640]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+4896]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+5152]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5408]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+4656]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+4912]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+5168]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+5424]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+4672]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+4928]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5184]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5440]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+4688]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+4944]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+5200]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+5456]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+4704]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+4960]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5216]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+5472]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+4720]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+4976]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5232]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5488]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu XMMWORD PTR [esi+592], xmm4
	movdqu XMMWORD PTR [esi+608], xmm2
	movdqu XMMWORD PTR [esi+624], xmm0
	movdqu XMMWORD PTR [esi+640], xmm3
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+5504]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+5760]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+6016]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+6272]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+5520]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5776]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+6032]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6288]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+5536]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+5792]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6048]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6304]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+5552]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5808]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+6064]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+6320]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+5568]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5824]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6080]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+6336]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+5584]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+5840]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+6096]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6352]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+5600]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5856]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6112]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+6368]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+5616]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+5872]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6128]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6384]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+5632]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+5888]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+6144]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+6400]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+5648]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+5904]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+6160]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6416]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+5664]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+5920]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6176]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6432]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+5680]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+5936]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+6192]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+6448]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+5696]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+5952]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6208]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+6464]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+5712]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+5968]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+6224]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6480]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+5728]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+5984]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6240]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+6496]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+5744]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6000]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6256]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6512]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu XMMWORD PTR [esi+656], xmm4
	movdqu XMMWORD PTR [esi+672], xmm2
	movdqu XMMWORD PTR [esi+688], xmm0
	movdqu XMMWORD PTR [esi+704], xmm3
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+6528]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+6784]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+7040]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+7296]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+6544]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6800]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7056]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7312]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+6560]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+6816]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7072]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+7328]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+6576]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6832]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+7088]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+7344]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+6592]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6848]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7104]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7360]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+6608]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+6864]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+7120]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7376]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+6624]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+6880]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7136]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+7392]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+6640]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+6896]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+7152]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7408]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+6656]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+6912]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+7168]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+7424]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+6672]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+6928]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7184]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7440]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+6688]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+6944]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7200]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+7456]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+6704]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+6960]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+7216]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+7472]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+6720]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+6976]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7232]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7488]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+6736]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+6992]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+7248]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7504]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+6752]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7008]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7264]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+7520]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+6768]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7024]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+7280]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7536]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu XMMWORD PTR [esi+720], xmm4
	movdqu XMMWORD PTR [esi+736], xmm2
	movdqu XMMWORD PTR [esi+752], xmm0
	movdqu XMMWORD PTR [esi+768], xmm3
	movdqu xmm0, XMMWORD PTR [esi+272]
	movdqu xmm1, XMMWORD PTR [edx+7552]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [edx+7808]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edx+8064]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [edx+8320]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [esi+288]
	movdqu xmm6, XMMWORD PTR [edx+7568]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7824]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+8080]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+8336]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+304]
	movdqu xmm3, XMMWORD PTR [edx+7584]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+7840]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+8096]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+8352]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+320]
	movdqu xmm0, XMMWORD PTR [edx+7600]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7856]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+8112]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+8368]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+336]
	movdqu xmm5, XMMWORD PTR [edx+7616]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+7872]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+8128]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+8384]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+352]
	movdqu xmm2, XMMWORD PTR [edx+7632]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+7888]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+8144]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+8400]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+368]
	movdqu xmm7, XMMWORD PTR [edx+7648]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+7904]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+8160]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+8416]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+384]
	movdqu xmm4, XMMWORD PTR [edx+7664]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+7920]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+8176]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+8432]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+400]
	movdqu xmm1, XMMWORD PTR [edx+7680]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+7936]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+8192]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+8448]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+416]
	movdqu xmm6, XMMWORD PTR [edx+7696]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+7952]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+8208]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+8464]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+432]
	movdqu xmm3, XMMWORD PTR [edx+7712]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+7968]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+8224]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+8480]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+448]
	movdqu xmm0, XMMWORD PTR [edx+7728]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+7984]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+8240]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+8496]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+464]
	movdqu xmm5, XMMWORD PTR [edx+7744]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+8000]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+8256]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+8512]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+480]
	movdqu xmm2, XMMWORD PTR [edx+7760]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edx+8016]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edx+8272]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+8528]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+496]
	movdqu xmm7, XMMWORD PTR [edx+7776]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edx+8032]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edx+8288]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edx+8544]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+512]
	movdqu xmm4, XMMWORD PTR [edx+7792]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edx+8048]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edx+8304]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edx+8560]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [edx+4352]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu XMMWORD PTR [esi+784], xmm4
	movdqu XMMWORD PTR [esi+800], xmm2
	movdqu XMMWORD PTR [esi+816], xmm0
	movdqu XMMWORD PTR [esi+832], xmm3
	ret
	.p2align 6
