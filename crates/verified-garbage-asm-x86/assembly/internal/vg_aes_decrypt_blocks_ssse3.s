// The functions of `src/internal/vg_aes_decrypt_blocks_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_decrypt_blocks_ssse3:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+704], ebx
	mov DWORD PTR [eax+708], esi
	mov DWORD PTR [eax+712], ebp
	mov DWORD PTR [eax+716], edi
	mov edi, eax
	mov eax, 218628480
	mov DWORD PTR [edi], eax
	mov eax, 235210255
	mov DWORD PTR [edi+4], eax
	mov eax, 168496130
	mov DWORD PTR [edi+8], eax
	mov eax, 67568393
	mov DWORD PTR [edi+12], eax
	mov eax, 201392768
	mov DWORD PTR [edi+16], eax
	mov eax, 168626952
	mov DWORD PTR [edi+20], eax
	mov eax, 84348420
	mov DWORD PTR [edi+24], eax
	mov eax, 252249603
	mov DWORD PTR [edi+28], eax
	mov eax, -1057474560
	mov DWORD PTR [edi+32], eax
	mov eax, -54262724
	mov DWORD PTR [edi+36], eax
	mov eax, -1951173813
	mov DWORD PTR [edi+40], eax
	mov eax, -1215344777
	mov DWORD PTR [edi+44], eax
	mov eax, 345396177
	mov DWORD PTR [edi+48], eax
	mov eax, 328291542
	mov DWORD PTR [edi+52], eax
	mov eax, 176704975
	mov DWORD PTR [edi+56], eax
	mov eax, 227494600
	mov DWORD PTR [edi+60], eax
	mov eax, -1570190848
	mov DWORD PTR [edi+64], eax
	mov eax, 1436499447
	mov DWORD PTR [edi+68], eax
	mov eax, -1233330668
	mov DWORD PTR [edi+72], eax
	mov eax, 1099639267
	mov DWORD PTR [edi+76], eax
	mov eax, 612476160
	mov DWORD PTR [edi+80], eax
	mov eax, -831827990
	mov DWORD PTR [edi+84], eax
	mov eax, -1808722512
	mov DWORD PTR [edi+88], eax
	mov eax, 2128346970
	mov DWORD PTR [edi+92], eax
	mov eax, 854835456
	mov DWORD PTR [edi+96], eax
	mov eax, -1789630809
	mov DWORD PTR [edi+100], eax
	mov eax, 703126043
	mov DWORD PTR [edi+104], eax
	mov eax, -1907393092
	mov DWORD PTR [edi+108], eax
	mov eax, -496005888
	mov DWORD PTR [edi+112], eax
	mov eax, 193357033
	mov DWORD PTR [edi+116], eax
	mov eax, -9269219
	mov DWORD PTR [edi+120], eax
	mov eax, 379288052
	mov DWORD PTR [edi+124], eax
	mov eax, -1447008000
	mov DWORD PTR [edi+128], eax
	mov eax, 1829023172
	mov DWORD PTR [edi+132], eax
	mov eax, -558424457
	mov DWORD PTR [edi+136], eax
	mov eax, 443800243
	mov DWORD PTR [edi+140], eax
	mov eax, 214288640
	mov DWORD PTR [edi+144], eax
	mov eax, 1283819840
	mov DWORD PTR [edi+148], eax
	mov eax, 366792729
	mov DWORD PTR [edi+152], eax
	mov eax, 1436323929
	mov DWORD PTR [edi+156], eax
	mov eax, 197121
	mov DWORD PTR [edi+160], eax
	mov eax, 67569157
	mov DWORD PTR [edi+164], eax
	mov eax, 134941193
	mov DWORD PTR [edi+168], eax
	mov eax, 202313229
	mov DWORD PTR [edi+172], eax
	mov eax, -1848775936
	mov DWORD PTR [edi+176], eax
	mov eax, -799269573
	mov DWORD PTR [edi+180], eax
	mov eax, 1737259690
	mov DWORD PTR [edi+184], eax
	mov eax, -1208598234
	mov DWORD PTR [edi+188], eax
	mov eax, -270403840
	mov DWORD PTR [edi+192], eax
	mov eax, 1007607243
	mov DWORD PTR [edi+196], eax
	mov eax, -986572764
	mov DWORD PTR [edi+200], eax
	mov eax, -114633962
	mov DWORD PTR [edi+204], eax
	mov eax, 999093760
	mov DWORD PTR [edi+208], eax
	mov eax, -340302051
	mov DWORD PTR [edi+212], eax
	mov eax, -1436758746
	mov DWORD PTR [edi+216], eax
	mov eax, 1100075130
	mov DWORD PTR [edi+220], eax
	mov eax, -885904896
	mov DWORD PTR [edi+224], eax
	mov eax, -134625827
	mov DWORD PTR [edi+228], eax
	mov eax, 604954902
	mov DWORD PTR [edi+232], eax
	mov eax, -739296232
	mov DWORD PTR [edi+236], eax
	mov eax, 1391471616
	mov DWORD PTR [edi+240], eax
	mov eax, 1654821454
	mov DWORD PTR [edi+244], eax
	mov eax, -322929124
	mov DWORD PTR [edi+248], eax
	mov eax, -1900138276
	mov DWORD PTR [edi+252], eax
	mov eax, 1241974784
	mov DWORD PTR [edi+256], eax
	mov eax, -1488084817
	mov DWORD PTR [edi+260], eax
	mov eax, -487963931
	mov DWORD PTR [edi+264], eax
	mov eax, 1168698639
	mov DWORD PTR [edi+268], eax
	mov eax, 1779655424
	mov DWORD PTR [edi+272], eax
	mov eax, -411437948
	mov DWORD PTR [edi+276], eax
	mov eax, -39974418
	mov DWORD PTR [edi+280], eax
	mov eax, 446139760
	mov DWORD PTR [edi+284], eax
	mov eax, -828793088
	mov DWORD PTR [edi+288], eax
	mov eax, -1000907429
	mov DWORD PTR [edi+292], eax
	mov eax, 210981269
	mov DWORD PTR [edi+296], eax
	mov eax, -926807546
	mov DWORD PTR [edi+300], eax
	mov eax, 118099200
	mov DWORD PTR [edi+304], eax
	mov eax, 185467140
	mov DWORD PTR [edi+308], eax
	mov eax, 251790600
	mov DWORD PTR [edi+312], eax
	mov eax, 50727180
	mov DWORD PTR [edi+316], eax
	mov eax, -106735104
	mov DWORD PTR [edi+320], eax
	mov eax, 1359737512
	mov DWORD PTR [edi+324], eax
	mov eax, -896505549
	mov DWORD PTR [edi+328], eax
	mov eax, 1647886747
	mov DWORD PTR [edi+332], eax
	mov eax, -557993263
	mov DWORD PTR [edi+336], eax
	mov eax, -1694894443
	mov DWORD PTR [edi+340], eax
	mov eax, 1947670651
	mov DWORD PTR [edi+344], eax
	mov eax, 810769471
	mov DWORD PTR [edi+348], eax
	mov eax, -1910662144
	mov DWORD PTR [edi+352], eax
	mov eax, -661404348
	mov DWORD PTR [edi+356], eax
	mov eax, -682945846
	mov DWORD PTR [edi+360], eax
	mov eax, 257513089
	mov DWORD PTR [edi+364], eax
	mov eax, -1715310848
	mov DWORD PTR [edi+368], eax
	mov eax, 73123435
	mov DWORD PTR [edi+372], eax
	mov eax, 811595506
	mov DWORD PTR [edi+376], eax
	mov eax, 883531181
	mov DWORD PTR [edi+380], eax
	mov eax, 252645135
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	movdqu xmm1, XMMWORD PTR [edi+160]
	movdqa xmm0, xmm1
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+384], xmm0
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+304]
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+416], xmm0
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+432], xmm0
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu xmm6, XMMWORD PTR [edi]
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov eax, ecx
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add esi, eax
	mov ebx, edi
	add ebx, 464
	sub ecx, 1
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu XMMWORD PTR [ebx], xmm0
20:
	sub esi, 16
	add ebx, 16
	movdqu xmm0, XMMWORD PTR [esi]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+32]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+48]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [edi+64]
	pshufb xmm4, xmm0
	movdqu xmm3, XMMWORD PTR [edi+80]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+160]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+96]
	pshufb xmm4, xmm0
	movdqu xmm3, XMMWORD PTR [edi+112]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+384]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+128]
	pshufb xmm4, xmm0
	movdqu xmm3, XMMWORD PTR [edi+144]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+400]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [ebx], xmm2
	sub ecx, 1
	jne 20b
	sub esi, 16
	add ebx, 16
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu XMMWORD PTR [ebx], xmm0
	mov esi, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	test ebp, ebp
	je 21f
23:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm1, XMMWORD PTR [edi+464]
	pxor xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+320]
	pshufb xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+336]
	pshufb xmm0, xmm1
	pxor xmm0, xmm2
	mov ebx, edi
	add ebx, 480
	mov ecx, DWORD PTR [esp+8]
	sub ecx, 1
24:
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+16]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+176]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+192]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+304]
	pshufb xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+208]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [edi+224]
	pshufb xmm4, xmm5
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [edi+416]
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+240]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [edi+256]
	pshufb xmm4, xmm5
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [edi+432]
	pshufb xmm3, xmm4
	movdqu xmm1, XMMWORD PTR [edi+272]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [edi+288]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+448]
	pshufb xmm1, xmm4
	pxor xmm3, xmm1
	pxor xmm0, xmm3
	add ebx, 16
	sub ecx, 1
	jne 24b
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+16]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+352]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+368]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+304]
	pshufb xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub ebp, 1
	jne 23b
	jmp 22f
21:
22:
	mov ebx, DWORD PTR [edi+704]
	mov esi, DWORD PTR [edi+708]
	mov ebp, DWORD PTR [edi+712]
	mov edi, DWORD PTR [edi+716]
	ret
	.p2align 6
