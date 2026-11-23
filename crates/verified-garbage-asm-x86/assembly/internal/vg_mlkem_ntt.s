// The functions of `src/internal/vg_mlkem_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_ntt:
	lea esp, [esp-12]
	stmxcsr DWORD PTR [esp+4]
	mov eax, 8127
	mov DWORD PTR [esp], eax
	ldmxcsr DWORD PTR [esp]
	lfence
	lea esp, [esp-4]
	mov eax, 218172673
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	mov eax, -217976063
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, DWORD PTR [esp+24]
	mov edx, 168495341
	mov DWORD PTR [eax], edx
	mov edx, 118754202
	mov DWORD PTR [eax+4], edx
	mov edx, 93193685
	mov DWORD PTR [eax+8], edx
	mov edx, 13238559
	mov DWORD PTR [eax+12], edx
	mov edx, 40766550
	mov DWORD PTR [eax+16], edx
	mov edx, 11929129
	mov DWORD PTR [eax+20], edx
	mov edx, 139396034
	mov DWORD PTR [eax+24], edx
	mov edx, 96208703
	mov DWORD PTR [eax+28], edx
	mov edx, 131334717
	mov DWORD PTR [eax+32], edx
	mov edx, 25100552
	mov DWORD PTR [eax+36], edx
	mov edx, 95553988
	mov DWORD PTR [eax+40], edx
	mov edx, 209651391
	mov DWORD PTR [eax+44], edx
	mov edx, 66652760
	mov DWORD PTR [eax+48], edx
	mov edx, 39846620
	mov DWORD PTR [eax+52], edx
	mov edx, 26937083
	mov DWORD PTR [eax+56], edx
	mov edx, 115215412
	mov DWORD PTR [eax+60], edx
	mov edx, 42730695
	mov DWORD PTR [eax+64], edx
	mov edx, 66521817
	mov DWORD PTR [eax+68], edx
	mov edx, 97716212
	mov DWORD PTR [eax+72], edx
	mov edx, 116984807
	mov DWORD PTR [eax+76], edx
	mov edx, 217645572
	mov DWORD PTR [eax+80], edx
	mov edx, 174525377
	mov DWORD PTR [eax+84], edx
	mov edx, 142018223
	mov DWORD PTR [eax+88], edx
	mov edx, 96272510
	mov DWORD PTR [eax+92], edx
	mov edx, 212273580
	mov DWORD PTR [eax+96], edx
	mov edx, 54397938
	mov DWORD PTR [eax+100], edx
	mov edx, 125042795
	mov DWORD PTR [eax+104], edx
	mov edx, 155847690
	mov DWORD PTR [eax+108], edx
	mov edx, 62983027
	mov DWORD PTR [eax+112], edx
	mov edx, 170657565
	mov DWORD PTR [eax+116], edx
	mov edx, 148373952
	mov DWORD PTR [eax+120], edx
	mov edx, 134611621
	mov DWORD PTR [eax+124], edx
	mov edx, 28182706
	mov DWORD PTR [eax+128], edx
	mov edx, 55247403
	mov DWORD PTR [eax+132], edx
	mov edx, 57083934
	mov DWORD PTR [eax+136], edx
	mov edx, 6882830
	mov DWORD PTR [eax+140], edx
	mov edx, 38470054
	mov DWORD PTR [eax+144], edx
	mov edx, 202768561
	mov DWORD PTR [eax+148], edx
	mov edx, 188025822
	mov DWORD PTR [eax+152], edx
	mov edx, 108332582
	mov DWORD PTR [eax+156], edx
	mov edx, 50990091
	mov DWORD PTR [eax+160], edx
	mov edx, 208536711
	mov DWORD PTR [eax+164], edx
	mov edx, 97192440
	mov DWORD PTR [eax+168], edx
	mov edx, 73337511
	mov DWORD PTR [eax+172], edx
	mov edx, 42206923
	mov DWORD PTR [eax+176], edx
	mov edx, 22874521
	mov DWORD PTR [eax+180], edx
	mov edx, 21561762
	mov DWORD PTR [eax+184], edx
	mov edx, 213257317
	mov DWORD PTR [eax+188], edx
	mov edx, 71893809
	mov DWORD PTR [eax+192], edx
	mov edx, 39977563
	mov DWORD PTR [eax+196], edx
	mov edx, 133956906
	mov DWORD PTR [eax+200], edx
	mov edx, 25167688
	mov DWORD PTR [eax+204], edx
	mov edx, 209258562
	mov DWORD PTR [eax+208], edx
	mov edx, 130680002
	mov DWORD PTR [eax+212], edx
	mov edx, 14420375
	mov DWORD PTR [eax+216], edx
	mov edx, 109447262
	mov DWORD PTR [eax+220], edx
	mov edx, 117901408
	mov DWORD PTR [eax+224], edx
	mov edx, 52037635
	mov DWORD PTR [eax+228], edx
	mov edx, 162203419
	mov DWORD PTR [eax+232], edx
	mov edx, 31328667
	mov DWORD PTR [eax+236], edx
	mov edx, 197987477
	mov DWORD PTR [eax+240], edx
	mov edx, 64947172
	mov DWORD PTR [eax+244], edx
	mov edx, 122487742
	mov DWORD PTR [eax+248], edx
	mov edx, 106694130
	mov DWORD PTR [eax+252], edx
	mov edx, eax
	add edx, 2
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov ecx, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
20:
	movdqu xmm0, XMMWORD PTR [ecx]
	movdqu xmm1, XMMWORD PTR [ecx+16]
	packssdw xmm0, xmm1
	movdqu XMMWORD PTR [eax], xmm0
	add ecx, 32
	add eax, 16
	cmp eax, DWORD PTR [esp+24]
	jne 20b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
21:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 0
	add edx, 2
	mov ecx, 16
22:
	movdqu xmm0, XMMWORD PTR [eax+256]
	movdqu xmm1, XMMWORD PTR [eax]
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqu XMMWORD PTR [eax], xmm3
	movdqu XMMWORD PTR [eax+256], xmm1
	add eax, 16
	sub ecx, 1
	jne 22b
	add eax, 256
	cmp eax, DWORD PTR [esp+24]
	jne 21b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
23:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 0
	add edx, 2
	mov ecx, 8
24:
	movdqu xmm0, XMMWORD PTR [eax+128]
	movdqu xmm1, XMMWORD PTR [eax]
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqu XMMWORD PTR [eax], xmm3
	movdqu XMMWORD PTR [eax+128], xmm1
	add eax, 16
	sub ecx, 1
	jne 24b
	add eax, 128
	cmp eax, DWORD PTR [esp+24]
	jne 23b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
25:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 0
	add edx, 2
	mov ecx, 4
26:
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu xmm1, XMMWORD PTR [eax]
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqu XMMWORD PTR [eax], xmm3
	movdqu XMMWORD PTR [eax+64], xmm1
	add eax, 16
	sub ecx, 1
	jne 26b
	add eax, 64
	cmp eax, DWORD PTR [esp+24]
	jne 25b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
27:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 0
	add edx, 2
	mov ecx, 2
28:
	movdqu xmm0, XMMWORD PTR [eax+32]
	movdqu xmm1, XMMWORD PTR [eax]
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqu XMMWORD PTR [eax], xmm3
	movdqu XMMWORD PTR [eax+32], xmm1
	add eax, 16
	sub ecx, 1
	jne 28b
	add eax, 32
	cmp eax, DWORD PTR [esp+24]
	jne 27b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
29:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 0
	add edx, 2
	mov ecx, 1
210:
	movdqu xmm0, XMMWORD PTR [eax+16]
	movdqu xmm1, XMMWORD PTR [eax]
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqu XMMWORD PTR [eax], xmm3
	movdqu XMMWORD PTR [eax+16], xmm1
	add eax, 16
	sub ecx, 1
	jne 210b
	add eax, 16
	cmp eax, DWORD PTR [esp+24]
	jne 29b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
211:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	pshufd xmm5, xmm5, 80
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+16]
	movdqa xmm1, xmm0
	punpckhqdq xmm0, xmm2
	punpcklqdq xmm1, xmm2
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqa xmm2, xmm3
	punpcklqdq xmm2, xmm1
	punpckhqdq xmm3, xmm1
	movdqu XMMWORD PTR [eax], xmm2
	movdqu XMMWORD PTR [eax+16], xmm3
	add eax, 32
	add edx, 4
	cmp eax, DWORD PTR [esp+24]
	jne 211b
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
212:
	movq xmm5, QWORD PTR [edx]
	punpcklwd xmm5, xmm5
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+16]
	pshufd xmm0, xmm0, 216
	pshufd xmm2, xmm2, 216
	movdqa xmm1, xmm0
	punpckhqdq xmm0, xmm2
	punpcklqdq xmm1, xmm2
	movdqa xmm2, xmm0
	pmullw xmm2, xmm5
	pmullw xmm2, xmm6
	pmulhw xmm0, xmm5
	pmulhw xmm2, xmm7
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm0, xmm2
	movdqa xmm3, xmm1
	paddw xmm3, xmm0
	psubw xmm3, xmm7
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm3, xmm2
	psubw xmm1, xmm0
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm7
	paddw xmm1, xmm2
	movdqa xmm2, xmm3
	punpckldq xmm2, xmm1
	punpckhdq xmm3, xmm1
	movdqu XMMWORD PTR [eax], xmm2
	movdqu XMMWORD PTR [eax+16], xmm3
	add eax, 32
	add edx, 8
	cmp eax, DWORD PTR [esp+24]
	jne 212b
	pxor xmm4, xmm4
	mov ecx, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+24]
	sub eax, 512
213:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [ecx], xmm0
	movdqu XMMWORD PTR [ecx+16], xmm1
	add ecx, 32
	add eax, 16
	cmp eax, DWORD PTR [esp+24]
	jne 213b
	lea esp, [esp+4]
	lfence
	ldmxcsr DWORD PTR [esp+4]
	lea esp, [esp+12]
	ret
	.p2align 6
