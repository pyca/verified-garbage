// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+4]
	mov DWORD PTR [eax+392], esi
	mov DWORD PTR [eax+396], edi
	mov DWORD PTR [eax+400], ebp
	mov edi, eax
	mov esi, ecx
	mov eax, 1
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
	mov eax, 32898
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 32906
	mov DWORD PTR [edi+216], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+220], eax
	mov eax, -2147450880
	mov DWORD PTR [edi+224], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+228], eax
	mov eax, 32907
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, -2147483647
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, -2147450751
	mov DWORD PTR [edi+248], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+252], eax
	mov eax, 32777
	mov DWORD PTR [edi+256], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+260], eax
	mov eax, 138
	mov DWORD PTR [edi+264], eax
	mov eax, 0
	mov DWORD PTR [edi+268], eax
	mov eax, 136
	mov DWORD PTR [edi+272], eax
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, -2147450871
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, -2147483638
	mov DWORD PTR [edi+288], eax
	mov eax, 0
	mov DWORD PTR [edi+292], eax
	mov eax, -2147450741
	mov DWORD PTR [edi+296], eax
	mov eax, 0
	mov DWORD PTR [edi+300], eax
	mov eax, 139
	mov DWORD PTR [edi+304], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+308], eax
	mov eax, 32905
	mov DWORD PTR [edi+312], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+316], eax
	mov eax, 32771
	mov DWORD PTR [edi+320], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+324], eax
	mov eax, 32770
	mov DWORD PTR [edi+328], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+332], eax
	mov eax, 128
	mov DWORD PTR [edi+336], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+340], eax
	mov eax, 32778
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -2147483638
	mov DWORD PTR [edi+352], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+356], eax
	mov eax, -2147450751
	mov DWORD PTR [edi+360], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+364], eax
	mov eax, 32896
	mov DWORD PTR [edi+368], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+372], eax
	mov eax, -2147483647
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, -2147450872
	mov DWORD PTR [edi+384], eax
	mov eax, -2147483648
	mov DWORD PTR [edi+388], eax
	mov ebp, edi
	add ebp, 200
20:
	movq xmm0, QWORD PTR [esi]
	movq xmm1, QWORD PTR [esi+40]
	pxor xmm0, xmm1
	movq xmm2, QWORD PTR [esi+80]
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+120]
	pxor xmm0, xmm3
	movq xmm4, QWORD PTR [esi+160]
	pxor xmm0, xmm4
	movq xmm5, QWORD PTR [esi+8]
	movq xmm6, QWORD PTR [esi+48]
	pxor xmm5, xmm6
	movq xmm7, QWORD PTR [esi+88]
	pxor xmm5, xmm7
	movq xmm1, QWORD PTR [esi+128]
	pxor xmm5, xmm1
	movq xmm2, QWORD PTR [esi+168]
	pxor xmm5, xmm2
	movq xmm3, QWORD PTR [esi+16]
	movq xmm4, QWORD PTR [esi+56]
	pxor xmm3, xmm4
	movq xmm6, QWORD PTR [esi+96]
	pxor xmm3, xmm6
	movq xmm7, QWORD PTR [esi+136]
	pxor xmm3, xmm7
	movq xmm1, QWORD PTR [esi+176]
	pxor xmm3, xmm1
	movq xmm2, QWORD PTR [esi+24]
	movq xmm4, QWORD PTR [esi+64]
	pxor xmm2, xmm4
	movq xmm6, QWORD PTR [esi+104]
	pxor xmm2, xmm6
	movq xmm7, QWORD PTR [esi+144]
	pxor xmm2, xmm7
	movq xmm1, QWORD PTR [esi+184]
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+32]
	movq xmm6, QWORD PTR [esi+72]
	pxor xmm4, xmm6
	movq xmm7, QWORD PTR [esi+112]
	pxor xmm4, xmm7
	movq xmm1, QWORD PTR [esi+152]
	pxor xmm4, xmm1
	movq xmm6, QWORD PTR [esi+192]
	pxor xmm4, xmm6
	movdqa xmm7, xmm5
	movdqa xmm1, xmm7
	psllq xmm7, 1
	psrlq xmm1, 63
	por xmm7, xmm1
	pxor xmm7, xmm4
	movq QWORD PTR [edi+448], xmm7
	movdqa xmm6, xmm2
	movdqa xmm1, xmm6
	psllq xmm6, 1
	psrlq xmm1, 63
	por xmm6, xmm1
	pxor xmm6, xmm5
	movq QWORD PTR [edi+464], xmm6
	movdqa xmm5, xmm0
	movdqa xmm7, xmm5
	psllq xmm5, 1
	psrlq xmm7, 63
	por xmm5, xmm7
	pxor xmm5, xmm2
	movq QWORD PTR [edi+480], xmm5
	movdqa xmm2, xmm3
	movdqa xmm1, xmm2
	psllq xmm2, 1
	psrlq xmm1, 63
	por xmm2, xmm1
	pxor xmm2, xmm0
	movq QWORD PTR [edi+456], xmm2
	movdqa xmm0, xmm4
	movdqa xmm6, xmm0
	psllq xmm0, 1
	psrlq xmm6, 63
	por xmm0, xmm6
	pxor xmm0, xmm3
	movq QWORD PTR [edi+472], xmm0
	movq xmm3, QWORD PTR [esi]
	movq xmm4, QWORD PTR [edi+448]
	pxor xmm3, xmm4
	movq xmm7, QWORD PTR [esi+48]
	movq xmm1, QWORD PTR [edi+456]
	pxor xmm7, xmm1
	movdqa xmm5, xmm7
	psllq xmm7, 44
	psrlq xmm5, 20
	por xmm7, xmm5
	movq xmm2, QWORD PTR [esi+96]
	movq xmm6, QWORD PTR [edi+464]
	pxor xmm2, xmm6
	movdqa xmm0, xmm2
	psllq xmm2, 43
	psrlq xmm0, 21
	por xmm2, xmm0
	movq xmm4, QWORD PTR [esi+144]
	movq xmm6, QWORD PTR [edi+472]
	pxor xmm4, xmm6
	movdqa xmm1, xmm4
	psllq xmm4, 21
	psrlq xmm1, 43
	por xmm4, xmm1
	movq xmm0, QWORD PTR [esi+192]
	movq xmm6, QWORD PTR [edi+480]
	pxor xmm0, xmm6
	movdqa xmm5, xmm0
	psllq xmm0, 14
	psrlq xmm5, 50
	por xmm0, xmm5
	movdqa xmm6, xmm2
	pandn xmm6, xmm4
	pxor xmm6, xmm7
	movq QWORD PTR [edi+8], xmm6
	movdqa xmm1, xmm3
	pandn xmm1, xmm7
	pxor xmm1, xmm0
	movq QWORD PTR [edi+32], xmm1
	movdqa xmm5, xmm0
	pandn xmm5, xmm3
	pxor xmm5, xmm4
	movq QWORD PTR [edi+24], xmm5
	pandn xmm7, xmm2
	pxor xmm7, xmm3
	movq xmm6, QWORD PTR [ebp]
	pxor xmm7, xmm6
	movq QWORD PTR [edi], xmm7
	pandn xmm4, xmm0
	pxor xmm4, xmm2
	movq QWORD PTR [edi+16], xmm4
	movq xmm3, QWORD PTR [esi+24]
	movq xmm2, QWORD PTR [edi+472]
	pxor xmm3, xmm2
	movdqa xmm2, xmm3
	psllq xmm3, 28
	psrlq xmm2, 36
	por xmm3, xmm2
	movq xmm2, QWORD PTR [esi+72]
	movq xmm0, QWORD PTR [edi+480]
	pxor xmm2, xmm0
	movdqa xmm1, xmm2
	psllq xmm2, 20
	psrlq xmm1, 44
	por xmm2, xmm1
	movq xmm0, QWORD PTR [esi+80]
	movq xmm6, QWORD PTR [edi+448]
	pxor xmm0, xmm6
	movdqa xmm4, xmm0
	psllq xmm0, 3
	psrlq xmm4, 61
	por xmm0, xmm4
	movq xmm5, QWORD PTR [esi+128]
	movq xmm7, QWORD PTR [edi+456]
	pxor xmm5, xmm7
	movdqa xmm6, xmm5
	psllq xmm5, 45
	psrlq xmm6, 19
	por xmm5, xmm6
	movq xmm1, QWORD PTR [esi+176]
	movq xmm7, QWORD PTR [edi+464]
	pxor xmm1, xmm7
	movdqa xmm7, xmm1
	psllq xmm1, 61
	psrlq xmm7, 3
	por xmm1, xmm7
	movdqa xmm4, xmm0
	pandn xmm4, xmm5
	pxor xmm4, xmm2
	movq QWORD PTR [edi+48], xmm4
	movdqa xmm6, xmm3
	pandn xmm6, xmm2
	pxor xmm6, xmm1
	movq QWORD PTR [edi+72], xmm6
	movdqa xmm7, xmm1
	pandn xmm7, xmm3
	pxor xmm7, xmm5
	movq QWORD PTR [edi+64], xmm7
	pandn xmm2, xmm0
	pxor xmm2, xmm3
	movq QWORD PTR [edi+40], xmm2
	pandn xmm5, xmm1
	pxor xmm5, xmm0
	movq QWORD PTR [edi+56], xmm5
	movq xmm3, QWORD PTR [esi+8]
	movq xmm0, QWORD PTR [edi+456]
	pxor xmm3, xmm0
	movdqa xmm0, xmm3
	psllq xmm3, 1
	psrlq xmm0, 63
	por xmm3, xmm0
	movq xmm2, QWORD PTR [esi+56]
	movq xmm1, QWORD PTR [edi+464]
	pxor xmm2, xmm1
	movdqa xmm4, xmm2
	psllq xmm2, 6
	psrlq xmm4, 58
	por xmm2, xmm4
	movq xmm6, QWORD PTR [esi+104]
	movq xmm1, QWORD PTR [edi+472]
	pxor xmm6, xmm1
	movdqa xmm5, xmm6
	psllq xmm6, 25
	psrlq xmm5, 39
	por xmm6, xmm5
	movq xmm0, QWORD PTR [esi+152]
	movq xmm1, QWORD PTR [edi+480]
	pxor xmm0, xmm1
	movdqa xmm7, xmm0
	psllq xmm0, 8
	psrlq xmm7, 56
	por xmm0, xmm7
	movq xmm1, QWORD PTR [esi+160]
	movq xmm4, QWORD PTR [edi+448]
	pxor xmm1, xmm4
	movdqa xmm5, xmm1
	psllq xmm1, 18
	psrlq xmm5, 46
	por xmm1, xmm5
	movdqa xmm4, xmm6
	pandn xmm4, xmm0
	pxor xmm4, xmm2
	movq QWORD PTR [edi+88], xmm4
	movdqa xmm7, xmm3
	pandn xmm7, xmm2
	pxor xmm7, xmm1
	movq QWORD PTR [edi+112], xmm7
	movdqa xmm5, xmm1
	pandn xmm5, xmm3
	pxor xmm5, xmm0
	movq QWORD PTR [edi+104], xmm5
	pandn xmm2, xmm6
	pxor xmm2, xmm3
	movq QWORD PTR [edi+80], xmm2
	pandn xmm0, xmm1
	pxor xmm0, xmm6
	movq QWORD PTR [edi+96], xmm0
	movq xmm3, QWORD PTR [esi+32]
	movq xmm6, QWORD PTR [edi+480]
	pxor xmm3, xmm6
	movdqa xmm6, xmm3
	psllq xmm3, 27
	psrlq xmm6, 37
	por xmm3, xmm6
	movq xmm2, QWORD PTR [esi+40]
	movq xmm4, QWORD PTR [edi+448]
	pxor xmm2, xmm4
	movdqa xmm1, xmm2
	psllq xmm2, 36
	psrlq xmm1, 28
	por xmm2, xmm1
	movq xmm7, QWORD PTR [esi+88]
	movq xmm6, QWORD PTR [edi+456]
	pxor xmm7, xmm6
	movdqa xmm4, xmm7
	psllq xmm7, 10
	psrlq xmm4, 54
	por xmm7, xmm4
	movq xmm0, QWORD PTR [esi+136]
	movq xmm6, QWORD PTR [edi+464]
	pxor xmm0, xmm6
	movdqa xmm5, xmm0
	psllq xmm0, 15
	psrlq xmm5, 49
	por xmm0, xmm5
	movq xmm6, QWORD PTR [esi+184]
	movq xmm1, QWORD PTR [edi+472]
	pxor xmm6, xmm1
	movdqa xmm4, xmm6
	psllq xmm6, 56
	psrlq xmm4, 8
	por xmm6, xmm4
	movdqa xmm1, xmm7
	pandn xmm1, xmm0
	pxor xmm1, xmm2
	movq QWORD PTR [edi+128], xmm1
	movdqa xmm5, xmm3
	pandn xmm5, xmm2
	pxor xmm5, xmm6
	movq QWORD PTR [edi+152], xmm5
	movdqa xmm4, xmm6
	pandn xmm4, xmm3
	pxor xmm4, xmm0
	movq QWORD PTR [edi+144], xmm4
	pandn xmm2, xmm7
	pxor xmm2, xmm3
	movq QWORD PTR [edi+120], xmm2
	pandn xmm0, xmm6
	pxor xmm0, xmm7
	movq QWORD PTR [edi+136], xmm0
	movq xmm3, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [edi+464]
	pxor xmm3, xmm7
	movdqa xmm7, xmm3
	psllq xmm3, 62
	psrlq xmm7, 2
	por xmm3, xmm7
	movq xmm2, QWORD PTR [esi+64]
	movq xmm1, QWORD PTR [edi+472]
	pxor xmm2, xmm1
	movdqa xmm6, xmm2
	psllq xmm2, 55
	psrlq xmm6, 9
	por xmm2, xmm6
	movq xmm5, QWORD PTR [esi+112]
	movq xmm7, QWORD PTR [edi+480]
	pxor xmm5, xmm7
	movdqa xmm1, xmm5
	psllq xmm5, 39
	psrlq xmm1, 25
	por xmm5, xmm1
	movq xmm0, QWORD PTR [esi+120]
	movq xmm7, QWORD PTR [edi+448]
	pxor xmm0, xmm7
	movdqa xmm4, xmm0
	psllq xmm0, 41
	psrlq xmm4, 23
	por xmm0, xmm4
	movq xmm7, QWORD PTR [esi+168]
	movq xmm6, QWORD PTR [edi+456]
	pxor xmm7, xmm6
	movdqa xmm1, xmm7
	psllq xmm7, 2
	psrlq xmm1, 62
	por xmm7, xmm1
	movdqa xmm6, xmm5
	pandn xmm6, xmm0
	pxor xmm6, xmm2
	movq QWORD PTR [edi+168], xmm6
	movdqa xmm4, xmm3
	pandn xmm4, xmm2
	pxor xmm4, xmm7
	movq QWORD PTR [edi+192], xmm4
	movdqa xmm1, xmm7
	pandn xmm1, xmm3
	pxor xmm1, xmm0
	movq QWORD PTR [edi+184], xmm1
	pandn xmm2, xmm5
	pxor xmm2, xmm3
	movq QWORD PTR [edi+160], xmm2
	pandn xmm0, xmm7
	pxor xmm0, xmm5
	movq QWORD PTR [edi+176], xmm0
	add ebp, 8
	movq xmm3, QWORD PTR [edi]
	movq xmm5, QWORD PTR [edi+40]
	pxor xmm3, xmm5
	movq xmm5, QWORD PTR [edi+80]
	pxor xmm3, xmm5
	movq xmm2, QWORD PTR [edi+120]
	pxor xmm3, xmm2
	movq xmm5, QWORD PTR [edi+160]
	pxor xmm3, xmm5
	movq xmm6, QWORD PTR [edi+8]
	movq xmm7, QWORD PTR [edi+48]
	pxor xmm6, xmm7
	movq xmm2, QWORD PTR [edi+88]
	pxor xmm6, xmm2
	movq xmm4, QWORD PTR [edi+128]
	pxor xmm6, xmm4
	movq xmm7, QWORD PTR [edi+168]
	pxor xmm6, xmm7
	movq xmm2, QWORD PTR [edi+16]
	movq xmm0, QWORD PTR [edi+56]
	pxor xmm2, xmm0
	movq xmm4, QWORD PTR [edi+96]
	pxor xmm2, xmm4
	movq xmm1, QWORD PTR [edi+136]
	pxor xmm2, xmm1
	movq xmm0, QWORD PTR [edi+176]
	pxor xmm2, xmm0
	movq xmm4, QWORD PTR [edi+24]
	movq xmm1, QWORD PTR [edi+64]
	pxor xmm4, xmm1
	movq xmm1, QWORD PTR [edi+104]
	pxor xmm4, xmm1
	movq xmm1, QWORD PTR [edi+144]
	pxor xmm4, xmm1
	movq xmm1, QWORD PTR [edi+184]
	pxor xmm4, xmm1
	movq xmm5, QWORD PTR [edi+32]
	movq xmm7, QWORD PTR [edi+72]
	pxor xmm5, xmm7
	movq xmm7, QWORD PTR [edi+112]
	pxor xmm5, xmm7
	movq xmm0, QWORD PTR [edi+152]
	pxor xmm5, xmm0
	movq xmm7, QWORD PTR [edi+192]
	pxor xmm5, xmm7
	movdqa xmm1, xmm6
	movdqa xmm0, xmm1
	psllq xmm1, 1
	psrlq xmm0, 63
	por xmm1, xmm0
	pxor xmm1, xmm5
	movq QWORD PTR [edi+448], xmm1
	movdqa xmm7, xmm4
	movdqa xmm0, xmm7
	psllq xmm7, 1
	psrlq xmm0, 63
	por xmm7, xmm0
	pxor xmm7, xmm6
	movq QWORD PTR [edi+464], xmm7
	movdqa xmm6, xmm3
	movdqa xmm1, xmm6
	psllq xmm6, 1
	psrlq xmm1, 63
	por xmm6, xmm1
	pxor xmm6, xmm4
	movq QWORD PTR [edi+480], xmm6
	movdqa xmm4, xmm2
	movdqa xmm0, xmm4
	psllq xmm4, 1
	psrlq xmm0, 63
	por xmm4, xmm0
	pxor xmm4, xmm3
	movq QWORD PTR [edi+456], xmm4
	movdqa xmm3, xmm5
	movdqa xmm7, xmm3
	psllq xmm3, 1
	psrlq xmm7, 63
	por xmm3, xmm7
	pxor xmm3, xmm2
	movq QWORD PTR [edi+472], xmm3
	movq xmm2, QWORD PTR [edi]
	movq xmm5, QWORD PTR [edi+448]
	pxor xmm2, xmm5
	movq xmm1, QWORD PTR [edi+48]
	movq xmm0, QWORD PTR [edi+456]
	pxor xmm1, xmm0
	movdqa xmm6, xmm1
	psllq xmm1, 44
	psrlq xmm6, 20
	por xmm1, xmm6
	movq xmm4, QWORD PTR [edi+96]
	movq xmm7, QWORD PTR [edi+464]
	pxor xmm4, xmm7
	movdqa xmm3, xmm4
	psllq xmm4, 43
	psrlq xmm3, 21
	por xmm4, xmm3
	movq xmm5, QWORD PTR [edi+144]
	movq xmm7, QWORD PTR [edi+472]
	pxor xmm5, xmm7
	movdqa xmm0, xmm5
	psllq xmm5, 21
	psrlq xmm0, 43
	por xmm5, xmm0
	movq xmm3, QWORD PTR [edi+192]
	movq xmm7, QWORD PTR [edi+480]
	pxor xmm3, xmm7
	movdqa xmm6, xmm3
	psllq xmm3, 14
	psrlq xmm6, 50
	por xmm3, xmm6
	movdqa xmm7, xmm4
	pandn xmm7, xmm5
	pxor xmm7, xmm1
	movq QWORD PTR [esi+8], xmm7
	movdqa xmm0, xmm2
	pandn xmm0, xmm1
	pxor xmm0, xmm3
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm3
	pandn xmm6, xmm2
	pxor xmm6, xmm5
	movq QWORD PTR [esi+24], xmm6
	pandn xmm1, xmm4
	pxor xmm1, xmm2
	movq xmm7, QWORD PTR [ebp]
	pxor xmm1, xmm7
	movq QWORD PTR [esi], xmm1
	pandn xmm5, xmm3
	pxor xmm5, xmm4
	movq QWORD PTR [esi+16], xmm5
	movq xmm2, QWORD PTR [edi+24]
	movq xmm4, QWORD PTR [edi+472]
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	psllq xmm2, 28
	psrlq xmm4, 36
	por xmm2, xmm4
	movq xmm4, QWORD PTR [edi+72]
	movq xmm3, QWORD PTR [edi+480]
	pxor xmm4, xmm3
	movdqa xmm0, xmm4
	psllq xmm4, 20
	psrlq xmm0, 44
	por xmm4, xmm0
	movq xmm3, QWORD PTR [edi+80]
	movq xmm7, QWORD PTR [edi+448]
	pxor xmm3, xmm7
	movdqa xmm5, xmm3
	psllq xmm3, 3
	psrlq xmm5, 61
	por xmm3, xmm5
	movq xmm6, QWORD PTR [edi+128]
	movq xmm1, QWORD PTR [edi+456]
	pxor xmm6, xmm1
	movdqa xmm7, xmm6
	psllq xmm6, 45
	psrlq xmm7, 19
	por xmm6, xmm7
	movq xmm0, QWORD PTR [edi+176]
	movq xmm1, QWORD PTR [edi+464]
	pxor xmm0, xmm1
	movdqa xmm1, xmm0
	psllq xmm0, 61
	psrlq xmm1, 3
	por xmm0, xmm1
	movdqa xmm5, xmm3
	pandn xmm5, xmm6
	pxor xmm5, xmm4
	movq QWORD PTR [esi+48], xmm5
	movdqa xmm7, xmm2
	pandn xmm7, xmm4
	pxor xmm7, xmm0
	movq QWORD PTR [esi+72], xmm7
	movdqa xmm1, xmm0
	pandn xmm1, xmm2
	pxor xmm1, xmm6
	movq QWORD PTR [esi+64], xmm1
	pandn xmm4, xmm3
	pxor xmm4, xmm2
	movq QWORD PTR [esi+40], xmm4
	pandn xmm6, xmm0
	pxor xmm6, xmm3
	movq QWORD PTR [esi+56], xmm6
	movq xmm2, QWORD PTR [edi+8]
	movq xmm3, QWORD PTR [edi+456]
	pxor xmm2, xmm3
	movdqa xmm3, xmm2
	psllq xmm2, 1
	psrlq xmm3, 63
	por xmm2, xmm3
	movq xmm4, QWORD PTR [edi+56]
	movq xmm0, QWORD PTR [edi+464]
	pxor xmm4, xmm0
	movdqa xmm5, xmm4
	psllq xmm4, 6
	psrlq xmm5, 58
	por xmm4, xmm5
	movq xmm7, QWORD PTR [edi+104]
	movq xmm0, QWORD PTR [edi+472]
	pxor xmm7, xmm0
	movdqa xmm6, xmm7
	psllq xmm7, 25
	psrlq xmm6, 39
	por xmm7, xmm6
	movq xmm3, QWORD PTR [edi+152]
	movq xmm0, QWORD PTR [edi+480]
	pxor xmm3, xmm0
	movdqa xmm1, xmm3
	psllq xmm3, 8
	psrlq xmm1, 56
	por xmm3, xmm1
	movq xmm0, QWORD PTR [edi+160]
	movq xmm5, QWORD PTR [edi+448]
	pxor xmm0, xmm5
	movdqa xmm6, xmm0
	psllq xmm0, 18
	psrlq xmm6, 46
	por xmm0, xmm6
	movdqa xmm5, xmm7
	pandn xmm5, xmm3
	pxor xmm5, xmm4
	movq QWORD PTR [esi+88], xmm5
	movdqa xmm1, xmm2
	pandn xmm1, xmm4
	pxor xmm1, xmm0
	movq QWORD PTR [esi+112], xmm1
	movdqa xmm6, xmm0
	pandn xmm6, xmm2
	pxor xmm6, xmm3
	movq QWORD PTR [esi+104], xmm6
	pandn xmm4, xmm7
	pxor xmm4, xmm2
	movq QWORD PTR [esi+80], xmm4
	pandn xmm3, xmm0
	pxor xmm3, xmm7
	movq QWORD PTR [esi+96], xmm3
	movq xmm2, QWORD PTR [edi+32]
	movq xmm7, QWORD PTR [edi+480]
	pxor xmm2, xmm7
	movdqa xmm7, xmm2
	psllq xmm2, 27
	psrlq xmm7, 37
	por xmm2, xmm7
	movq xmm4, QWORD PTR [edi+40]
	movq xmm5, QWORD PTR [edi+448]
	pxor xmm4, xmm5
	movdqa xmm0, xmm4
	psllq xmm4, 36
	psrlq xmm0, 28
	por xmm4, xmm0
	movq xmm1, QWORD PTR [edi+88]
	movq xmm7, QWORD PTR [edi+456]
	pxor xmm1, xmm7
	movdqa xmm5, xmm1
	psllq xmm1, 10
	psrlq xmm5, 54
	por xmm1, xmm5
	movq xmm3, QWORD PTR [edi+136]
	movq xmm7, QWORD PTR [edi+464]
	pxor xmm3, xmm7
	movdqa xmm6, xmm3
	psllq xmm3, 15
	psrlq xmm6, 49
	por xmm3, xmm6
	movq xmm7, QWORD PTR [edi+184]
	movq xmm0, QWORD PTR [edi+472]
	pxor xmm7, xmm0
	movdqa xmm5, xmm7
	psllq xmm7, 56
	psrlq xmm5, 8
	por xmm7, xmm5
	movdqa xmm0, xmm1
	pandn xmm0, xmm3
	pxor xmm0, xmm4
	movq QWORD PTR [esi+128], xmm0
	movdqa xmm6, xmm2
	pandn xmm6, xmm4
	pxor xmm6, xmm7
	movq QWORD PTR [esi+152], xmm6
	movdqa xmm5, xmm7
	pandn xmm5, xmm2
	pxor xmm5, xmm3
	movq QWORD PTR [esi+144], xmm5
	pandn xmm4, xmm1
	pxor xmm4, xmm2
	movq QWORD PTR [esi+120], xmm4
	pandn xmm3, xmm7
	pxor xmm3, xmm1
	movq QWORD PTR [esi+136], xmm3
	movq xmm2, QWORD PTR [edi+16]
	movq xmm1, QWORD PTR [edi+464]
	pxor xmm2, xmm1
	movdqa xmm1, xmm2
	psllq xmm2, 62
	psrlq xmm1, 2
	por xmm2, xmm1
	movq xmm4, QWORD PTR [edi+64]
	movq xmm0, QWORD PTR [edi+472]
	pxor xmm4, xmm0
	movdqa xmm7, xmm4
	psllq xmm4, 55
	psrlq xmm7, 9
	por xmm4, xmm7
	movq xmm6, QWORD PTR [edi+112]
	movq xmm1, QWORD PTR [edi+480]
	pxor xmm6, xmm1
	movdqa xmm0, xmm6
	psllq xmm6, 39
	psrlq xmm0, 25
	por xmm6, xmm0
	movq xmm3, QWORD PTR [edi+120]
	movq xmm1, QWORD PTR [edi+448]
	pxor xmm3, xmm1
	movdqa xmm5, xmm3
	psllq xmm3, 41
	psrlq xmm5, 23
	por xmm3, xmm5
	movq xmm1, QWORD PTR [edi+168]
	movq xmm7, QWORD PTR [edi+456]
	pxor xmm1, xmm7
	movdqa xmm0, xmm1
	psllq xmm1, 2
	psrlq xmm0, 62
	por xmm1, xmm0
	movdqa xmm7, xmm6
	pandn xmm7, xmm3
	pxor xmm7, xmm4
	movq QWORD PTR [esi+168], xmm7
	movdqa xmm5, xmm2
	pandn xmm5, xmm4
	pxor xmm5, xmm1
	movq QWORD PTR [esi+192], xmm5
	movdqa xmm0, xmm1
	pandn xmm0, xmm2
	pxor xmm0, xmm3
	movq QWORD PTR [esi+184], xmm0
	pandn xmm4, xmm6
	pxor xmm4, xmm2
	movq QWORD PTR [esi+160], xmm4
	pandn xmm3, xmm1
	pxor xmm3, xmm6
	movq QWORD PTR [esi+176], xmm3
	add ebp, 8
	mov eax, ebp
	sub eax, edi
	cmp eax, 392
	jne 20b
	mov esi, DWORD PTR [edi+392]
	mov ebp, DWORD PTR [edi+400]
	mov edi, DWORD PTR [edi+396]
	ret
	.p2align 6
