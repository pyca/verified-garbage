// The functions of `src/internal/vg_mlkem_multiply_ntts.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_multiply_ntts:
	lea esp, [esp-12]
	stmxcsr DWORD PTR [esp+4]
	mov eax, 8127
	mov DWORD PTR [esp], eax
	ldmxcsr DWORD PTR [esp]
	lfence
	push ebx
	mov eax, 218172673
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	mov eax, -217976063
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, 88671561
	movd xmm4, eax
	pshufd xmm4, xmm4, 0
	mov eax, DWORD PTR [esp+32]
	mov edx, 72288434
	mov DWORD PTR [eax], edx
	mov edx, 189989294
	mov DWORD PTR [eax+4], edx
	mov edx, 181797419
	mov DWORD PTR [eax+8], edx
	mov edx, 162923339
	mov DWORD PTR [eax+12], edx
	mov edx, 81987614
	mov DWORD PTR [eax+16], edx
	mov edx, 161088359
	mov DWORD PTR [eax+20], edx
	mov edx, 116590094
	mov DWORD PTR [eax+24], edx
	mov edx, 211288169
	mov DWORD PTR [eax+28], edx
	mov edx, 190513574
	mov DWORD PTR [eax+32], edx
	mov edx, 179700299
	mov DWORD PTR [eax+36], edx
	mov edx, 206569649
	mov DWORD PTR [eax+40], edx
	mov edx, 15404054
	mov DWORD PTR [eax+44], edx
	mov edx, 19074014
	mov DWORD PTR [eax+48], edx
	mov edx, 30149429
	mov DWORD PTR [eax+52], edx
	mov edx, 115017254
	mov DWORD PTR [eax+56], edx
	mov edx, 109839989
	mov DWORD PTR [eax+60], edx
	mov edx, 16124939
	mov DWORD PTR [eax+64], edx
	mov edx, 167183114
	mov DWORD PTR [eax+68], edx
	mov edx, 142214279
	mov DWORD PTR [eax+72], edx
	mov edx, 9636974
	mov DWORD PTR [eax+76], edx
	mov edx, 50924024
	mov DWORD PTR [eax+80], edx
	mov edx, 120980939
	mov DWORD PTR [eax+84], edx
	mov edx, 39455399
	mov DWORD PTR [eax+88], edx
	mov edx, 144835679
	mov DWORD PTR [eax+92], edx
	mov edx, 104203979
	mov DWORD PTR [eax+96], edx
	mov edx, 175964804
	mov DWORD PTR [eax+100], edx
	mov edx, 57149849
	mov DWORD PTR [eax+104], edx
	mov edx, 195297629
	mov DWORD PTR [eax+108], edx
	mov edx, 190775714
	mov DWORD PTR [eax+112], edx
	mov edx, 196608329
	mov DWORD PTR [eax+116], edx
	mov edx, 10226789
	mov DWORD PTR [eax+120], edx
	mov edx, 4918454
	mov DWORD PTR [eax+124], edx
	mov edx, 164627249
	mov DWORD PTR [eax+128], edx
	mov edx, 146277449
	mov DWORD PTR [eax+132], edx
	mov edx, 178651739
	mov DWORD PTR [eax+136], edx
	mov edx, 178192994
	mov DWORD PTR [eax+140], edx
	mov edx, 131532074
	mov DWORD PTR [eax+144], edx
	mov edx, 84215804
	mov DWORD PTR [eax+148], edx
	mov edx, 96012104
	mov DWORD PTR [eax+152], edx
	mov edx, 193003904
	mov DWORD PTR [eax+156], edx
	mov edx, 79628354
	mov DWORD PTR [eax+160], edx
	mov edx, 8916089
	mov DWORD PTR [eax+164], edx
	mov edx, 138347714
	mov DWORD PTR [eax+168], edx
	mov edx, 87492554
	mov DWORD PTR [eax+172], edx
	mov edx, 57280919
	mov DWORD PTR [eax+176], edx
	mov edx, 203751644
	mov DWORD PTR [eax+180], edx
	mov edx, 77793374
	mov DWORD PTR [eax+184], edx
	mov edx, 108725894
	mov DWORD PTR [eax+188], edx
	mov edx, 77662304
	mov DWORD PTR [eax+192], edx
	mov edx, 100271879
	mov DWORD PTR [eax+196], edx
	mov edx, 83757059
	mov DWORD PTR [eax+200], edx
	mov edx, 166134554
	mov DWORD PTR [eax+204], edx
	mov edx, 98961179
	mov DWORD PTR [eax+208], edx
	mov edx, 55970219
	mov DWORD PTR [eax+212], edx
	mov edx, 57018779
	mov DWORD PTR [eax+216], edx
	mov edx, 186843614
	mov DWORD PTR [eax+220], edx
	mov edx, 7081109
	mov DWORD PTR [eax+224], edx
	mov edx, 20188109
	mov DWORD PTR [eax+228], edx
	mov edx, 152896484
	mov DWORD PTR [eax+232], edx
	mov edx, 153224159
	mov DWORD PTR [eax+236], edx
	mov edx, 155386814
	mov DWORD PTR [eax+240], edx
	mov edx, 95684429
	mov DWORD PTR [eax+244], edx
	mov edx, 118425074
	mov DWORD PTR [eax+248], edx
	mov edx, 111478364
	mov DWORD PTR [eax+252], edx
	mov edx, eax
	mov ebx, DWORD PTR [esp+20]
	mov eax, ebx
	add eax, 1024
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+24]
	mov ecx, DWORD PTR [esp+28]
20:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+16]
	packssdw xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ecx]
	movdqu xmm2, XMMWORD PTR [ecx+16]
	packssdw xmm1, xmm2
	pshuflw xmm5, xmm1, 177
	pshufhw xmm5, xmm5, 177
	movdqa xmm3, xmm0
	movdqa xmm2, xmm3
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm3, xmm5
	pmulhw xmm2, xmm7
	psubw xmm3, xmm2
	movdqa xmm2, xmm0
	pmullw xmm2, xmm1
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm1
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	movdqa xmm1, xmm0
	movdqa xmm2, xmm1
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm1, xmm5
	pmulhw xmm2, xmm7
	psubw xmm1, xmm2
	psrld xmm1, 16
	paddw xmm0, xmm1
	movdqa xmm1, xmm3
	psrld xmm1, 16
	paddw xmm3, xmm1
	pslld xmm0, 16
	psrld xmm0, 16
	pslld xmm3, 16
	por xmm0, xmm3
	movdqa xmm2, xmm0
	pmullw xmm2, xmm4
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm4
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm1, xmm0
	pxor xmm2, xmm2
	punpcklwd xmm0, xmm2
	punpckhwd xmm1, xmm2
	movdqu XMMWORD PTR [ebx], xmm0
	movdqu XMMWORD PTR [ebx+16], xmm1
	add eax, 32
	add ecx, 32
	add edx, 8
	add ebx, 32
	cmp ebx, DWORD PTR [esp+32]
	jne 20b
	pop ebx
	lfence
	ldmxcsr DWORD PTR [esp+4]
	lea esp, [esp+12]
	ret
	.p2align 6
