// The functions of `src/internal/vg_mlkem768_decrypt_mul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_decrypt_mul:
	mov QWORD PTR [rcx+3072], rbp
	mov QWORD PTR [rcx+3080], r12
	mov QWORD PTR [rcx+3088], r13
	mov QWORD PTR [rcx+3096], r14
	mov QWORD PTR [rcx+3104], r15
	mov QWORD PTR [rcx+3112], rbx
	mov rbx, rcx
	mov rbp, rdi
	mov r12, rsi
	mov r13, rdx
	mov r14d, 3
	stmxcsr DWORD PTR [rbx+768]
	mov r11d, DWORD PTR [rbx+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rbx+772], eax
	ldmxcsr DWORD PTR [rbx+772]
	lfence
	mov rcx, rbx
	mov rdi, rbp
	pxor xmm0, xmm0
	mov ecx, 64
20:
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	sub rcx, 1
	jne 20b
21:
	mov rdi, r13
	mov rsi, rbx
	mov r10, rbx
	add r10, 1024
	movabs r9, 510045414021073133
	mov QWORD PTR [rsi], r9
	movabs r9, 56859178044360149
	mov QWORD PTR [rsi+8], r9
	movabs r9, 51235218965531734
	mov QWORD PTR [rsi+16], r9
	movabs r9, 413213233114973122
	mov QWORD PTR [rsi+24], r9
	movabs r9, 107806050082882109
	mov QWORD PTR [rsi+32], r9
	movabs r9, 900445868001462724
	mov QWORD PTR [rsi+40], r9
	movabs r9, 171139929822792280
	mov QWORD PTR [rsi+48], r9
	movabs r9, 494846426562103035
	mov QWORD PTR [rsi+56], r9
	movabs r9, 285709028528227527
	mov QWORD PTR [rsi+64], r9
	movabs r9, 502445920291588084
	mov QWORD PTR [rsi+72], r9
	movabs r9, 749580786754716164
	mov QWORD PTR [rsi+80], r9
	movabs r9, 413487282095851183
	mov QWORD PTR [rsi+88], r9
	movabs r9, 233637364892109228
	mov QWORD PTR [rsi+96], r9
	movabs r9, 669360731832189035
	mov QWORD PTR [rsi+104], r9
	movabs r9, 732968660552977267
	mov QWORD PTR [rsi+112], r9
	movabs r9, 578152510004920768
	mov QWORD PTR [rsi+120], r9
	movabs r9, 237285789102114994
	mov QWORD PTR [rsi+128], r9
	movabs r9, 29561529811011614
	mov QWORD PTR [rsi+136], r9
	movabs r9, 870884338190451110
	mov QWORD PTR [rsi+144], r9
	movabs r9, 465284896969264094
	mov QWORD PTR [rsi+152], r9
	movabs r9, 895658353811393547
	mov QWORD PTR [rsi+160], r9
	movabs r9, 314982211412232696
	mov QWORD PTR [rsi+168], r9
	movabs r9, 98245319648872139
	mov QWORD PTR [rsi+176], r9
	movabs r9, 915933202169266594
	mov QWORD PTR [rsi+184], r9
	movabs r9, 171702325730673457
	mov QWORD PTR [rsi+192], r9
	movabs r9, 108094397009888554
	mov QWORD PTR [rsi+200], r9
	movabs r9, 561266335040473154
	mov QWORD PTR [rsi+208], r9
	movabs r9, 470072410941163927
	mov QWORD PTR [rsi+216], r9
	movabs r9, 223499940604086368
	mov QWORD PTR [rsi+224], r9
	movabs r9, 134555600354477851
	mov QWORD PTR [rsi+232], r9
	movabs r9, 278945979905674389
	mov QWORD PTR [rsi+240], r9
	movabs r9, 458247799147660222
	mov QWORD PTR [rsi+248], r9
	mov eax, 218172673
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, -217976063
	movq xmm14, rax
	pshufd xmm14, xmm14, 0
	mov r9, rdi
	mov rdx, rsi
	add rdx, 256
	mov ecx, 32
22:
	movdqu xmm0, XMMWORD PTR [r9]
	movdqu xmm1, XMMWORD PTR [r9+16]
	packssdw xmm0, xmm1
	movdqu XMMWORD PTR [rdx], xmm0
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 22b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 2
	mov eax, 1
23:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, 2
	mov ecx, 16
24:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+256]
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+256], xmm3
	add rdx, 16
	sub rcx, 1
	jne 24b
	add rdx, 256
	sub rax, 1
	jne 23b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 4
	mov eax, 2
25:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, 2
	mov ecx, 8
26:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+128]
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+128], xmm3
	add rdx, 16
	sub rcx, 1
	jne 26b
	add rdx, 128
	sub rax, 1
	jne 25b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 8
	mov eax, 4
27:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, 2
	mov ecx, 4
28:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+64]
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+64], xmm3
	add rdx, 16
	sub rcx, 1
	jne 28b
	add rdx, 64
	sub rax, 1
	jne 27b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 16
	mov eax, 8
29:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, 2
	mov ecx, 2
210:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+32]
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+32], xmm3
	add rdx, 16
	sub rcx, 1
	jne 210b
	add rdx, 32
	sub rax, 1
	jne 29b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 32
	mov eax, 16
211:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, 2
	mov ecx, 1
212:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm3
	add rdx, 16
	sub rcx, 1
	jne 212b
	add rdx, 16
	sub rax, 1
	jne 211b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 64
	mov ecx, 16
213:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 80
	add r8, 4
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm2
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm3
	punpckhqdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 213b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 128
	mov ecx, 16
214:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm2, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 228
	add r8, 8
	pshufd xmm0, xmm0, 216
	pshufd xmm2, xmm2, 216
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm1, xmm2
	movdqa xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	psubw xmm3, xmm1
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqa xmm1, xmm0
	punpckldq xmm0, xmm3
	punpckhdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 214b
	mov rdi, r10
	mov r9, rdi
	mov rdx, rsi
	add rdx, 256
	pxor xmm4, xmm4
	mov ecx, 32
215:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [r9], xmm0
	movdqu XMMWORD PTR [r9+16], xmm1
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 215b
	mov rdi, rbp
	mov rsi, r12
	mov rdx, rbx
	add rdx, 1024
	mov rcx, rbx
	mov rdi, rcx
	add rdi, 2048
	mov r10, rcx
	movabs r9, 815997804392417458
	mov QWORD PTR [r10], r9
	movabs r9, 699750412941918763
	mov QWORD PTR [r10+8], r9
	movabs r9, 691869233753294878
	mov QWORD PTR [r10+16], r9
	movabs r9, 907475776003311118
	mov QWORD PTR [r10+24], r9
	movabs r9, 771806907476935078
	mov QWORD PTR [r10+32], r9
	movabs r9, 66159908362387633
	mov QWORD PTR [r10+40], r9
	movabs r9, 129490811567147998
	mov QWORD PTR [r10+48], r9
	movabs r9, 471759160663016998
	mov QWORD PTR [r10+56], r9
	movabs r9, 718046007089564683
	mov QWORD PTR [r10+64], r9
	movabs r9, 41390488304616583
	mov QWORD PTR [r10+72], r9
	movabs r9, 519609176495294968
	mov QWORD PTR [r10+80], r9
	movabs r9, 622064504638409383
	mov QWORD PTR [r10+88], r9
	movabs r9, 755763078531253963
	mov QWORD PTR [r10+96], r9
	movabs r9, 838796929598491033
	mov QWORD PTR [r10+104], r9
	movabs r9, 844426343366984098
	mov QWORD PTR [r10+112], r9
	movabs r9, 21124599087107173
	mov QWORD PTR [r10+120], r9
	movabs r9, 628256859761935153
	mov QWORD PTR [r10+128], r9
	movabs r9, 765333081784975963
	mov QWORD PTR [r10+136], r9
	movabs r9, 361704124117878058
	mov QWORD PTR [r10+144], r9
	movabs r9, 828945455776335688
	mov QWORD PTR [r10+152], r9
	movabs r9, 38294310742853698
	mov QWORD PTR [r10+160], r9
	movabs r9, 375777658211861698
	mov QWORD PTR [r10+168], r9
	movabs r9, 875106647543515543
	mov QWORD PTR [r10+176], r9
	movabs r9, 466974159036155998
	mov QWORD PTR [r10+184], r9
	movabs r9, 430664441091131488
	mov QWORD PTR [r10+192], r9
	movabs r9, 713542476249303043
	mov QWORD PTR [r10+200], r9
	movabs r9, 240390260253919003
	mov QWORD PTR [r10+208], r9
	movabs r9, 802487211653466523
	mov QWORD PTR [r10+216], r9
	movabs r9, 86707267930164373
	mov QWORD PTR [r10+224], r9
	movabs r9, 658092752015000548
	mov QWORD PTR [r10+232], r9
	movabs r9, 410961493446820798
	mov QWORD PTR [r10+240], r9
	movabs r9, 478795927710008818
	mov QWORD PTR [r10+248], r9
	mov eax, 218172673
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, -217976063
	movq xmm14, rax
	pshufd xmm14, xmm14, 0
	mov eax, 88671561
	movq xmm12, rax
	pshufd xmm12, xmm12, 0
	mov r8, r10
	mov ecx, 16
216:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	movdqu xmm2, XMMWORD PTR [rsi+32]
	movdqu xmm3, XMMWORD PTR [rsi+48]
	pshufd xmm0, xmm0, 216
	pshufd xmm1, xmm1, 216
	pshufd xmm2, xmm2, 216
	pshufd xmm3, xmm3, 216
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	punpckhqdq xmm5, xmm3
	packssdw xmm0, xmm2
	packssdw xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [rdx]
	movdqu xmm7, XMMWORD PTR [rdx+16]
	movdqu xmm8, XMMWORD PTR [rdx+32]
	movdqu xmm9, XMMWORD PTR [rdx+48]
	pshufd xmm6, xmm6, 216
	pshufd xmm7, xmm7, 216
	pshufd xmm8, xmm8, 216
	pshufd xmm9, xmm9, 216
	movdqa xmm10, xmm6
	punpcklqdq xmm6, xmm7
	punpckhqdq xmm10, xmm7
	movdqa xmm11, xmm8
	punpcklqdq xmm8, xmm9
	punpckhqdq xmm11, xmm9
	packssdw xmm6, xmm8
	packssdw xmm10, xmm11
	movdqu xmm13, XMMWORD PTR [r8]
	movdqa xmm1, xmm4
	movdqa xmm2, xmm1
	pmullw xmm2, xmm10
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm10
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm1
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm1, xmm13
	pmulhw xmm2, xmm15
	psubw xmm1, xmm2
	movdqa xmm2, xmm0
	movdqa xmm3, xmm2
	pmullw xmm3, xmm6
	pmullw xmm3, xmm14
	pmulhw xmm2, xmm6
	pmulhw xmm3, xmm15
	psubw xmm2, xmm3
	paddw xmm1, xmm2
	movdqa xmm2, xmm0
	movdqa xmm3, xmm2
	pmullw xmm3, xmm10
	pmullw xmm3, xmm14
	pmulhw xmm2, xmm10
	pmulhw xmm3, xmm15
	psubw xmm2, xmm3
	movdqa xmm3, xmm4
	pmullw xmm3, xmm6
	pmullw xmm3, xmm14
	pmulhw xmm4, xmm6
	pmulhw xmm3, xmm15
	psubw xmm4, xmm3
	paddw xmm2, xmm4
	movdqa xmm3, xmm1
	pmullw xmm3, xmm12
	pmullw xmm3, xmm14
	pmulhw xmm1, xmm12
	pmulhw xmm3, xmm15
	psubw xmm1, xmm3
	movdqa xmm3, xmm1
	psraw xmm3, 15
	pand xmm3, xmm15
	paddw xmm1, xmm3
	movdqa xmm3, xmm2
	pmullw xmm3, xmm12
	pmullw xmm3, xmm14
	pmulhw xmm2, xmm12
	pmulhw xmm3, xmm15
	psubw xmm2, xmm3
	movdqa xmm3, xmm2
	psraw xmm3, 15
	pand xmm3, xmm15
	paddw xmm2, xmm3
	movdqa xmm3, xmm1
	punpcklwd xmm1, xmm2
	punpckhwd xmm3, xmm2
	pxor xmm4, xmm4
	movdqa xmm5, xmm1
	punpcklwd xmm1, xmm4
	punpckhwd xmm5, xmm4
	movdqa xmm6, xmm3
	punpcklwd xmm3, xmm4
	punpckhwd xmm6, xmm4
	movdqu XMMWORD PTR [rdi], xmm1
	movdqu XMMWORD PTR [rdi+16], xmm5
	movdqu XMMWORD PTR [rdi+32], xmm3
	movdqu XMMWORD PTR [rdi+48], xmm6
	add rsi, 64
	add rdx, 64
	add rdi, 64
	add r8, 16
	sub rcx, 1
	jne 216b
	mov rdi, rbp
	add rdi, 0
	mov rsi, rbx
	add rsi, 2048
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov ecx, 64
217:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	paddd xmm0, xmm1
	psubd xmm0, xmm15
	movdqa xmm1, xmm0
	psrad xmm1, 31
	pand xmm1, xmm15
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 217b
	add r12, 1024
	add r13, 1024
	sub r14, 1
	jne 21b
	mov rdi, rbp
	mov rsi, rbx
	movabs r9, 510045414021073133
	mov QWORD PTR [rsi], r9
	movabs r9, 56859178044360149
	mov QWORD PTR [rsi+8], r9
	movabs r9, 51235218965531734
	mov QWORD PTR [rsi+16], r9
	movabs r9, 413213233114973122
	mov QWORD PTR [rsi+24], r9
	movabs r9, 107806050082882109
	mov QWORD PTR [rsi+32], r9
	movabs r9, 900445868001462724
	mov QWORD PTR [rsi+40], r9
	movabs r9, 171139929822792280
	mov QWORD PTR [rsi+48], r9
	movabs r9, 494846426562103035
	mov QWORD PTR [rsi+56], r9
	movabs r9, 285709028528227527
	mov QWORD PTR [rsi+64], r9
	movabs r9, 502445920291588084
	mov QWORD PTR [rsi+72], r9
	movabs r9, 749580786754716164
	mov QWORD PTR [rsi+80], r9
	movabs r9, 413487282095851183
	mov QWORD PTR [rsi+88], r9
	movabs r9, 233637364892109228
	mov QWORD PTR [rsi+96], r9
	movabs r9, 669360731832189035
	mov QWORD PTR [rsi+104], r9
	movabs r9, 732968660552977267
	mov QWORD PTR [rsi+112], r9
	movabs r9, 578152510004920768
	mov QWORD PTR [rsi+120], r9
	movabs r9, 237285789102114994
	mov QWORD PTR [rsi+128], r9
	movabs r9, 29561529811011614
	mov QWORD PTR [rsi+136], r9
	movabs r9, 870884338190451110
	mov QWORD PTR [rsi+144], r9
	movabs r9, 465284896969264094
	mov QWORD PTR [rsi+152], r9
	movabs r9, 895658353811393547
	mov QWORD PTR [rsi+160], r9
	movabs r9, 314982211412232696
	mov QWORD PTR [rsi+168], r9
	movabs r9, 98245319648872139
	mov QWORD PTR [rsi+176], r9
	movabs r9, 915933202169266594
	mov QWORD PTR [rsi+184], r9
	movabs r9, 171702325730673457
	mov QWORD PTR [rsi+192], r9
	movabs r9, 108094397009888554
	mov QWORD PTR [rsi+200], r9
	movabs r9, 561266335040473154
	mov QWORD PTR [rsi+208], r9
	movabs r9, 470072410941163927
	mov QWORD PTR [rsi+216], r9
	movabs r9, 223499940604086368
	mov QWORD PTR [rsi+224], r9
	movabs r9, 134555600354477851
	mov QWORD PTR [rsi+232], r9
	movabs r9, 278945979905674389
	mov QWORD PTR [rsi+240], r9
	movabs r9, 458247799147660222
	mov QWORD PTR [rsi+248], r9
	mov eax, 218172673
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, -217976063
	movq xmm14, rax
	pshufd xmm14, xmm14, 0
	mov r9, rdi
	mov rdx, rsi
	add rdx, 256
	mov ecx, 32
218:
	movdqu xmm0, XMMWORD PTR [r9]
	movdqu xmm1, XMMWORD PTR [r9+16]
	packssdw xmm0, xmm1
	movdqu XMMWORD PTR [rdx], xmm0
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 218b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 248
	mov ecx, 16
219:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm2, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 27
	add r8, -8
	pshufd xmm0, xmm0, 216
	pshufd xmm2, xmm2, 216
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqa xmm1, xmm0
	punpckldq xmm0, xmm3
	punpckhdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 219b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 124
	mov ecx, 16
220:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 5
	add r8, -4
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm2
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm3
	punpckhqdq xmm1, xmm3
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	add rdx, 32
	sub rcx, 1
	jne 220b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 62
	mov eax, 16
221:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, -2
	mov ecx, 1
222:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm3
	add rdx, 16
	sub rcx, 1
	jne 222b
	add rdx, 16
	sub rax, 1
	jne 221b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 30
	mov eax, 8
223:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, -2
	mov ecx, 2
224:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+32]
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+32], xmm3
	add rdx, 16
	sub rcx, 1
	jne 224b
	add rdx, 32
	sub rax, 1
	jne 223b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 14
	mov eax, 4
225:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, -2
	mov ecx, 4
226:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+64]
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+64], xmm3
	add rdx, 16
	sub rcx, 1
	jne 226b
	add rdx, 64
	sub rax, 1
	jne 225b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 6
	mov eax, 2
227:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, -2
	mov ecx, 8
228:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+128]
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+128], xmm3
	add rdx, 16
	sub rcx, 1
	jne 228b
	add rdx, 128
	sub rax, 1
	jne 227b
	mov rdx, rsi
	add rdx, 256
	mov r8, rsi
	add r8, 2
	mov eax, 1
229:
	movdqu xmm13, XMMWORD PTR [r8]
	punpcklwd xmm13, xmm13
	pshufd xmm13, xmm13, 0
	add r8, -2
	mov ecx, 16
230:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+256]
	movdqa xmm3, xmm1
	psubw xmm3, xmm0
	paddw xmm0, xmm1
	psubw xmm0, xmm15
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm0, xmm2
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+256], xmm3
	add rdx, 16
	sub rcx, 1
	jne 230b
	add rdx, 256
	sub rax, 1
	jne 229b
	mov rdx, rsi
	add rdx, 256
	mov eax, 33554944
	movq xmm13, rax
	pshufd xmm13, xmm13, 0
	mov ecx, 32
231:
	movdqu xmm3, XMMWORD PTR [rdx]
	movdqa xmm2, xmm3
	pmullw xmm2, xmm13
	pmullw xmm2, xmm14
	pmulhw xmm3, xmm13
	pmulhw xmm2, xmm15
	psubw xmm3, xmm2
	movdqa xmm2, xmm3
	psraw xmm2, 15
	pand xmm2, xmm15
	paddw xmm3, xmm2
	movdqu XMMWORD PTR [rdx], xmm3
	add rdx, 16
	sub rcx, 1
	jne 231b
	mov r9, rdi
	mov rdx, rsi
	add rdx, 256
	pxor xmm4, xmm4
	mov ecx, 32
232:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [r9], xmm0
	movdqu XMMWORD PTR [r9+16], xmm1
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 232b
	lfence
	mov DWORD PTR [rbx+768], r11d
	ldmxcsr DWORD PTR [rbx+768]
	mov rbp, QWORD PTR [rbx+3072]
	mov r12, QWORD PTR [rbx+3080]
	mov r13, QWORD PTR [rbx+3088]
	mov r14, QWORD PTR [rbx+3096]
	mov r15, QWORD PTR [rbx+3104]
	mov rbx, QWORD PTR [rbx+3112]
	ret
	.p2align 6
