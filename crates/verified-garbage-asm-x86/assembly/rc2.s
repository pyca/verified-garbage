// The functions of `src/rc2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	lea esp, [esp-608]
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+632]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	sub ecx, 1
	cmp ecx, 128
	jae 20f
	mov eax, 2
	mov ecx, DWORD PTR [esp+12]
	sub ecx, 1
	cmp ecx, 1024
	jae 22f
	mov eax, 3
	mov ecx, DWORD PTR [esp+20]
	cmp ecx, 8
	jne 24f
	mov eax, 0
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	test eax, eax
	jne 26f
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+24]
	mov edx, DWORD PTR [eax]
	mov DWORD PTR [ecx+128], edx
	mov edx, DWORD PTR [eax+4]
	mov DWORD PTR [ecx+132], edx
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov ebx, eax
	mov esi, ecx
	mov edx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+4]
	push ebx
	push esi
	push edx
	push ecx
	push eax
	call {vg_rc2_expand_key}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebx+516]
	mov ebx, DWORD PTR [ebx+512]
	mov eax, 0
	jmp 27f
26:
27:
	mov ecx, 0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	lea esp, [esp+608]
	ret
	.p2align 6

vg_rc2_cbc_encrypt_update:
	lea esp, [esp-608]
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+632]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov ecx, DWORD PTR [esp+24]
	test ecx, ecx
	je 20f
	mov esi, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [esi+136]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+24]
	mov eax, DWORD PTR [esp+8]
	sub ecx, eax
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	jmp 26f
25:
26:
	mov edx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+24]
	sub ecx, eax
	mov eax, DWORD PTR [esp+8]
	add ecx, eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+136], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	jmp 21f
20:
	mov esi, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	add edx, ecx
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+136], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
21:
	mov ebx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, eax
	add ecx, 128
	mov edx, DWORD PTR [esp+20]
	mov esi, DWORD PTR [esp+24]
	shr esi, 3
	je 214f
	push ebx
	push esi
	push edx
	push ecx
	push eax
	call {vg_rc2_cbc_encrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebx+516]
	mov ebx, DWORD PTR [ebx+512]
	mov ecx, 0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	lea esp, [esp+608]
	ret
	.p2align 6

vg_rc2_cbc_decrypt_update:
	lea esp, [esp-608]
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+632]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov ecx, DWORD PTR [esp+24]
	test ecx, ecx
	je 20f
	mov esi, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [esi+136]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+24]
	mov eax, DWORD PTR [esp+8]
	sub ecx, eax
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	jmp 26f
25:
26:
	mov edx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+24]
	sub ecx, eax
	mov eax, DWORD PTR [esp+8]
	add ecx, eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+136], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	jmp 21f
20:
	mov esi, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	add edx, ecx
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+136], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
21:
	mov ebx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, eax
	add ecx, 128
	mov edx, DWORD PTR [esp+20]
	mov esi, DWORD PTR [esp+24]
	shr esi, 3
	je 214f
	push ebx
	push esi
	push edx
	push ecx
	push eax
	call {vg_rc2_cbc_decrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebx+516]
	mov ebx, DWORD PTR [ebx+512]
	mov ecx, 0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	lea esp, [esp+608]
	ret
	.p2align 6

vg_rc2_cbc_encrypt:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+264], ebp
	mov DWORD PTR [eax+268], ebx
	mov DWORD PTR [eax+272], esi
	mov DWORD PTR [eax+276], edi
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+16]
	cmp edi, 0
	je 20f
22:
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ecx]
	xor edx, DWORD PTR [ecx+4]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], edx
	push ebp
	push esi
	push ebx
	call {vg_rc2_encrypt_block}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add esi, 8
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+264]
	mov ebx, DWORD PTR [eax+268]
	mov esi, DWORD PTR [eax+272]
	mov edi, DWORD PTR [eax+276]
	ret
	.p2align 6

vg_rc2_cbc_decrypt:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+264], ebp
	mov DWORD PTR [eax+268], ebx
	mov DWORD PTR [eax+272], esi
	mov DWORD PTR [eax+276], edi
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+16]
	cmp edi, 0
	je 20f
22:
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+260], edx
	push ebp
	push esi
	push ebx
	call {vg_rc2_decrypt_block}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ecx]
	xor edx, DWORD PTR [ecx+4]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], edx
	mov eax, DWORD PTR [ebp+256]
	mov edx, DWORD PTR [ebp+260]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add esi, 8
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+264]
	mov ebx, DWORD PTR [eax+268]
	mov esi, DWORD PTR [eax+272]
	mov edi, DWORD PTR [eax+276]
	ret
	.p2align 6

vg_rc2_expand_key:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov ebp, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+16]
	mov ecx, 0
20:
	mov edx, ebp
	add edx, ecx
	movzx eax, BYTE PTR [edx]
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	add ecx, 1
	cmp ecx, esi
	jne 20b
	cmp ecx, 128
	jne 21f
	jmp 22f
21:
23:
	mov edx, edi
	add edx, ecx
	sub edx, 1
	movzx eax, BYTE PTR [edx]
	mov ebx, ecx
	sub ebx, esi
	mov edx, edi
	add edx, ebx
	movzx ebx, BYTE PTR [edx]
	add eax, ebx
	and eax, 255
	mov ebx, eax
	shr eax, 2
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 17
	mov edx, 2
	movd xmm3, edx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov edx, 4
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	mov edx, -1
	movd xmm6, edx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	mov edx, -990283559
	movd xmm5, edx
	mov edx, -306848487
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 2046683432
	movd xmm4, edx
	mov edx, -1646747574
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2093515066
	movd xmm5, edx
	mov edx, -1907132885
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -2006692766
	movd xmm4, edx
	mov edx, -1560573116
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -178677225
	movd xmm5, edx
	mov edx, 323990407
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1922218655
	movd xmm4, edx
	mov edx, 847085833
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -348090435
	movd xmm5, edx
	mov edx, 192657286
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 572626416
	movd xmm4, edx
	mov edx, -2108789924
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1822042540
	movd xmm5, edx
	mov edx, 481452238
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 348149363
	movd xmm4, edx
	mov edx, -588149593
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 533361938
	movd xmm5, edx
	mov edx, -773538245
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 819215682
	movd xmm4, edx
	mov edx, 649477283
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -636567697
	movd xmm5, edx
	mov edx, 1460103494
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1692536281
	movd xmm4, edx
	mov edx, 54760636
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -154725896
	movd xmm5, edx
	mov edx, -415305840
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 802538246
	movd xmm4, edx
	mov edx, -685873464
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -555030520
	movd xmm5, edx
	mov edx, -135376256
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1401771388
	movd xmm4, edx
	mov edx, 711609653
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1909594774
	movd xmm5, edx
	mov edx, 1950946650
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1590730571
	movd xmm4, edx
	mov edx, -324790268
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1849811138
	movd xmm5, edx
	mov edx, -859090673
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1353683236
	movd xmm4, edx
	mov edx, 963703969
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2059764583
	movd xmm5, edx
	mov edx, 2058663971
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1530266364
	movd xmm4, edx
	mov edx, 832001317
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1728422611
	movd xmm5, edx
	mov edx, -1366127901
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 271179525
	movd xmm4, edx
	mov edx, -910529433
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -807010093
	movd xmm5, edx
	mov edx, 749248225
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1057035875
	movd xmm4, edx
	mov edx, -1450581416
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 456407053
	movd xmm5, edx
	mov edx, -1325452373
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1594640571
	movd xmm4, edx
	mov edx, 785232313
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1205597125
	movd xmm5, edx
	mov edx, 2006754789
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1746970122
	movd xmm4, edx
	mov edx, -1379827714
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	pshufd xmm4, xmm1, 78
	por xmm1, xmm4
	pshufd xmm4, xmm1, 177
	por xmm1, xmm4
	mov edx, ebx
	shr edx, 1
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 0
	movdqa xmm4, xmm1
	psrld xmm4, 16
	pxor xmm4, xmm1
	pand xmm4, xmm2
	pxor xmm1, xmm4
	mov edx, ebx
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	movdqa xmm4, xmm1
	psrld xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	add ecx, 1
	cmp ecx, 128
	jne 23b
22:
	mov esi, DWORD PTR [esp+12]
	add esi, 7
	shr esi, 3
	mov ecx, 128
	sub ecx, esi
	mov edx, DWORD PTR [esp+12]
	and edx, 7
	mov ebx, 255
	cmp edx, 1
	je 24f
	jmp 25f
24:
	mov ebx, 1
25:
	cmp edx, 2
	je 26f
	jmp 27f
26:
	mov ebx, 3
27:
	cmp edx, 3
	je 28f
	jmp 29f
28:
	mov ebx, 7
29:
	cmp edx, 4
	je 210f
	jmp 211f
210:
	mov ebx, 15
211:
	cmp edx, 5
	je 212f
	jmp 213f
212:
	mov ebx, 31
213:
	cmp edx, 6
	je 214f
	jmp 215f
214:
	mov ebx, 63
215:
	cmp edx, 7
	je 216f
	jmp 217f
216:
	mov ebx, 127
217:
	mov edx, edi
	add edx, ecx
	movzx eax, BYTE PTR [edx]
	and eax, ebx
	and eax, 255
	mov ebx, eax
	shr eax, 2
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 17
	mov edx, 2
	movd xmm3, edx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov edx, 4
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	mov edx, -1
	movd xmm6, edx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	mov edx, -990283559
	movd xmm5, edx
	mov edx, -306848487
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 2046683432
	movd xmm4, edx
	mov edx, -1646747574
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2093515066
	movd xmm5, edx
	mov edx, -1907132885
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -2006692766
	movd xmm4, edx
	mov edx, -1560573116
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -178677225
	movd xmm5, edx
	mov edx, 323990407
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1922218655
	movd xmm4, edx
	mov edx, 847085833
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -348090435
	movd xmm5, edx
	mov edx, 192657286
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 572626416
	movd xmm4, edx
	mov edx, -2108789924
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1822042540
	movd xmm5, edx
	mov edx, 481452238
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 348149363
	movd xmm4, edx
	mov edx, -588149593
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 533361938
	movd xmm5, edx
	mov edx, -773538245
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 819215682
	movd xmm4, edx
	mov edx, 649477283
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -636567697
	movd xmm5, edx
	mov edx, 1460103494
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1692536281
	movd xmm4, edx
	mov edx, 54760636
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -154725896
	movd xmm5, edx
	mov edx, -415305840
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 802538246
	movd xmm4, edx
	mov edx, -685873464
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -555030520
	movd xmm5, edx
	mov edx, -135376256
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1401771388
	movd xmm4, edx
	mov edx, 711609653
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1909594774
	movd xmm5, edx
	mov edx, 1950946650
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1590730571
	movd xmm4, edx
	mov edx, -324790268
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1849811138
	movd xmm5, edx
	mov edx, -859090673
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1353683236
	movd xmm4, edx
	mov edx, 963703969
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2059764583
	movd xmm5, edx
	mov edx, 2058663971
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1530266364
	movd xmm4, edx
	mov edx, 832001317
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1728422611
	movd xmm5, edx
	mov edx, -1366127901
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 271179525
	movd xmm4, edx
	mov edx, -910529433
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -807010093
	movd xmm5, edx
	mov edx, 749248225
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1057035875
	movd xmm4, edx
	mov edx, -1450581416
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 456407053
	movd xmm5, edx
	mov edx, -1325452373
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1594640571
	movd xmm4, edx
	mov edx, 785232313
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1205597125
	movd xmm5, edx
	mov edx, 2006754789
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1746970122
	movd xmm4, edx
	mov edx, -1379827714
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	pshufd xmm4, xmm1, 78
	por xmm1, xmm4
	pshufd xmm4, xmm1, 177
	por xmm1, xmm4
	mov edx, ebx
	shr edx, 1
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 0
	movdqa xmm4, xmm1
	psrld xmm4, 16
	pxor xmm4, xmm1
	pand xmm4, xmm2
	pxor xmm1, xmm4
	mov edx, ebx
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	movdqa xmm4, xmm1
	psrld xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	cmp ecx, 0
	jne 218f
	jmp 219f
218:
220:
	sub ecx, 1
	mov edx, edi
	add edx, ecx
	add edx, 1
	movzx eax, BYTE PTR [edx]
	mov ebx, ecx
	add ebx, esi
	mov edx, edi
	add edx, ebx
	movzx ebx, BYTE PTR [edx]
	xor eax, ebx
	and eax, 255
	mov ebx, eax
	shr eax, 2
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 17
	mov edx, 2
	movd xmm3, edx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov edx, 4
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	mov edx, -1
	movd xmm6, edx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	mov edx, -990283559
	movd xmm5, edx
	mov edx, -306848487
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 2046683432
	movd xmm4, edx
	mov edx, -1646747574
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2093515066
	movd xmm5, edx
	mov edx, -1907132885
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -2006692766
	movd xmm4, edx
	mov edx, -1560573116
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -178677225
	movd xmm5, edx
	mov edx, 323990407
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1922218655
	movd xmm4, edx
	mov edx, 847085833
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -348090435
	movd xmm5, edx
	mov edx, 192657286
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 572626416
	movd xmm4, edx
	mov edx, -2108789924
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1822042540
	movd xmm5, edx
	mov edx, 481452238
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 348149363
	movd xmm4, edx
	mov edx, -588149593
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 533361938
	movd xmm5, edx
	mov edx, -773538245
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 819215682
	movd xmm4, edx
	mov edx, 649477283
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -636567697
	movd xmm5, edx
	mov edx, 1460103494
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1692536281
	movd xmm4, edx
	mov edx, 54760636
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -154725896
	movd xmm5, edx
	mov edx, -415305840
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 802538246
	movd xmm4, edx
	mov edx, -685873464
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -555030520
	movd xmm5, edx
	mov edx, -135376256
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, -1401771388
	movd xmm4, edx
	mov edx, 711609653
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1909594774
	movd xmm5, edx
	mov edx, 1950946650
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1590730571
	movd xmm4, edx
	mov edx, -324790268
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1849811138
	movd xmm5, edx
	mov edx, -859090673
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1353683236
	movd xmm4, edx
	mov edx, 963703969
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -2059764583
	movd xmm5, edx
	mov edx, 2058663971
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1530266364
	movd xmm4, edx
	mov edx, 832001317
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -1728422611
	movd xmm5, edx
	mov edx, -1366127901
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 271179525
	movd xmm4, edx
	mov edx, -910529433
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, -807010093
	movd xmm5, edx
	mov edx, 749248225
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1057035875
	movd xmm4, edx
	mov edx, -1450581416
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 456407053
	movd xmm5, edx
	mov edx, -1325452373
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1594640571
	movd xmm4, edx
	mov edx, 785232313
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	mov edx, 1205597125
	movd xmm5, edx
	mov edx, 2006754789
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov edx, 1746970122
	movd xmm4, edx
	mov edx, -1379827714
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	pshufd xmm4, xmm1, 78
	por xmm1, xmm4
	pshufd xmm4, xmm1, 177
	por xmm1, xmm4
	mov edx, ebx
	shr edx, 1
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm2, edx
	pshufd xmm2, xmm2, 0
	movdqa xmm4, xmm1
	psrld xmm4, 16
	pxor xmm4, xmm1
	pand xmm4, xmm2
	pxor xmm1, xmm4
	mov edx, ebx
	and edx, 1
	xor edx, -1
	add edx, 1
	movd xmm3, edx
	pshufd xmm3, xmm3, 0
	movdqa xmm4, xmm1
	psrld xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	cmp ecx, 0
	jne 220b
219:
	mov eax, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	ret
	.p2align 6

vg_rc2_encrypt_block:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov DWORD PTR [eax+16], ecx
	mov ebp, eax
	mov edi, DWORD PTR [esp+8]
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [edi+1]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+64], eax
	movzx eax, BYTE PTR [edi+2]
	movzx edx, BYTE PTR [edi+3]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+68], eax
	movzx eax, BYTE PTR [edi+4]
	movzx edx, BYTE PTR [edi+5]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+72], eax
	movzx eax, BYTE PTR [edi+6]
	movzx edx, BYTE PTR [edi+7]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi]
	movzx edi, BYTE PTR [edi+1]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+2]
	movzx edi, BYTE PTR [edi+3]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+4]
	movzx edi, BYTE PTR [edi+5]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+6]
	movzx edi, BYTE PTR [edi+7]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+8]
	movzx edi, BYTE PTR [edi+9]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+10]
	movzx edi, BYTE PTR [edi+11]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+12]
	movzx edi, BYTE PTR [edi+13]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+14]
	movzx edi, BYTE PTR [edi+15]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+16]
	movzx edi, BYTE PTR [edi+17]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+18]
	movzx edi, BYTE PTR [edi+19]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+20]
	movzx edi, BYTE PTR [edi+21]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+22]
	movzx edi, BYTE PTR [edi+23]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+24]
	movzx edi, BYTE PTR [edi+25]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+26]
	movzx edi, BYTE PTR [edi+27]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+28]
	movzx edi, BYTE PTR [edi+29]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+30]
	movzx edi, BYTE PTR [edi+31]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+32]
	movzx edi, BYTE PTR [edi+33]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+34]
	movzx edi, BYTE PTR [edi+35]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+36]
	movzx edi, BYTE PTR [edi+37]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+38]
	movzx edi, BYTE PTR [edi+39]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+40]
	movzx edi, BYTE PTR [edi+41]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+42]
	movzx edi, BYTE PTR [edi+43]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+44]
	movzx edi, BYTE PTR [edi+45]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+46]
	movzx edi, BYTE PTR [edi+47]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+48]
	movzx edi, BYTE PTR [edi+49]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+50]
	movzx edi, BYTE PTR [edi+51]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+52]
	movzx edi, BYTE PTR [edi+53]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+54]
	movzx edi, BYTE PTR [edi+55]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+56]
	movzx edi, BYTE PTR [edi+57]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+58]
	movzx edi, BYTE PTR [edi+59]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+60]
	movzx edi, BYTE PTR [edi+61]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+62]
	movzx edi, BYTE PTR [edi+63]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+64]
	movzx edi, BYTE PTR [edi+65]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+66]
	movzx edi, BYTE PTR [edi+67]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+68]
	movzx edi, BYTE PTR [edi+69]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+70]
	movzx edi, BYTE PTR [edi+71]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+72]
	movzx edi, BYTE PTR [edi+73]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+74]
	movzx edi, BYTE PTR [edi+75]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+76]
	movzx edi, BYTE PTR [edi+77]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+78]
	movzx edi, BYTE PTR [edi+79]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+80]
	movzx edi, BYTE PTR [edi+81]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+82]
	movzx edi, BYTE PTR [edi+83]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+84]
	movzx edi, BYTE PTR [edi+85]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+86]
	movzx edi, BYTE PTR [edi+87]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+88]
	movzx edi, BYTE PTR [edi+89]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+90]
	movzx edi, BYTE PTR [edi+91]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+92]
	movzx edi, BYTE PTR [edi+93]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+94]
	movzx edi, BYTE PTR [edi+95]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+96]
	movzx edi, BYTE PTR [edi+97]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+98]
	movzx edi, BYTE PTR [edi+99]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+100]
	movzx edi, BYTE PTR [edi+101]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+102]
	movzx edi, BYTE PTR [edi+103]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+104]
	movzx edi, BYTE PTR [edi+105]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+106]
	movzx edi, BYTE PTR [edi+107]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+108]
	movzx edi, BYTE PTR [edi+109]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+110]
	movzx edi, BYTE PTR [edi+111]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+112]
	movzx edi, BYTE PTR [edi+113]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+114]
	movzx edi, BYTE PTR [edi+115]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+116]
	movzx edi, BYTE PTR [edi+117]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+118]
	movzx edi, BYTE PTR [edi+119]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+120]
	movzx edi, BYTE PTR [edi+121]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+122]
	movzx edi, BYTE PTR [edi+123]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+124]
	movzx edi, BYTE PTR [edi+125]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+126]
	movzx edi, BYTE PTR [edi+127]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov edi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebp+64]
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	mov eax, DWORD PTR [ebp+68]
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	mov eax, DWORD PTR [ebp+72]
	mov BYTE PTR [edi+4], al
	shr eax, 8
	mov BYTE PTR [edi+5], al
	mov eax, DWORD PTR [ebp+76]
	mov BYTE PTR [edi+6], al
	shr eax, 8
	mov BYTE PTR [edi+7], al
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov ecx, DWORD PTR [eax+16]
	ret
	.p2align 6

vg_rc2_decrypt_block:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov DWORD PTR [eax+16], ecx
	mov ebp, eax
	mov edi, DWORD PTR [esp+8]
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [edi+1]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+64], eax
	movzx eax, BYTE PTR [edi+2]
	movzx edx, BYTE PTR [edi+3]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+68], eax
	movzx eax, BYTE PTR [edi+4]
	movzx edx, BYTE PTR [edi+5]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+72], eax
	movzx eax, BYTE PTR [edi+6]
	movzx edx, BYTE PTR [edi+7]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+126]
	movzx edi, BYTE PTR [edi+127]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+124]
	movzx edi, BYTE PTR [edi+125]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+122]
	movzx edi, BYTE PTR [edi+123]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+120]
	movzx edi, BYTE PTR [edi+121]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+118]
	movzx edi, BYTE PTR [edi+119]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+116]
	movzx edi, BYTE PTR [edi+117]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+114]
	movzx edi, BYTE PTR [edi+115]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+112]
	movzx edi, BYTE PTR [edi+113]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+110]
	movzx edi, BYTE PTR [edi+111]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+108]
	movzx edi, BYTE PTR [edi+109]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+106]
	movzx edi, BYTE PTR [edi+107]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+104]
	movzx edi, BYTE PTR [edi+105]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+102]
	movzx edi, BYTE PTR [edi+103]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+100]
	movzx edi, BYTE PTR [edi+101]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+98]
	movzx edi, BYTE PTR [edi+99]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+96]
	movzx edi, BYTE PTR [edi+97]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+94]
	movzx edi, BYTE PTR [edi+95]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+92]
	movzx edi, BYTE PTR [edi+93]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+90]
	movzx edi, BYTE PTR [edi+91]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+88]
	movzx edi, BYTE PTR [edi+89]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+86]
	movzx edi, BYTE PTR [edi+87]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+84]
	movzx edi, BYTE PTR [edi+85]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+82]
	movzx edi, BYTE PTR [edi+83]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+80]
	movzx edi, BYTE PTR [edi+81]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+78]
	movzx edi, BYTE PTR [edi+79]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+76]
	movzx edi, BYTE PTR [edi+77]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+74]
	movzx edi, BYTE PTR [edi+75]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+72]
	movzx edi, BYTE PTR [edi+73]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+70]
	movzx edi, BYTE PTR [edi+71]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+68]
	movzx edi, BYTE PTR [edi+69]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+66]
	movzx edi, BYTE PTR [edi+67]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+64]
	movzx edi, BYTE PTR [edi+65]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+62]
	movzx edi, BYTE PTR [edi+63]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+60]
	movzx edi, BYTE PTR [edi+61]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+58]
	movzx edi, BYTE PTR [edi+59]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+56]
	movzx edi, BYTE PTR [edi+57]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+54]
	movzx edi, BYTE PTR [edi+55]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+52]
	movzx edi, BYTE PTR [edi+53]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+50]
	movzx edi, BYTE PTR [edi+51]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+48]
	movzx edi, BYTE PTR [edi+49]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+46]
	movzx edi, BYTE PTR [edi+47]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+44]
	movzx edi, BYTE PTR [edi+45]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+42]
	movzx edi, BYTE PTR [edi+43]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+40]
	movzx edi, BYTE PTR [edi+41]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	sub edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+38]
	movzx edi, BYTE PTR [edi+39]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+36]
	movzx edi, BYTE PTR [edi+37]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+34]
	movzx edi, BYTE PTR [edi+35]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+32]
	movzx edi, BYTE PTR [edi+33]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+30]
	movzx edi, BYTE PTR [edi+31]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+28]
	movzx edi, BYTE PTR [edi+29]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+26]
	movzx edi, BYTE PTR [edi+27]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+24]
	movzx edi, BYTE PTR [edi+25]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+22]
	movzx edi, BYTE PTR [edi+23]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+20]
	movzx edi, BYTE PTR [edi+21]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+18]
	movzx edi, BYTE PTR [edi+19]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+16]
	movzx edi, BYTE PTR [edi+17]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+14]
	movzx edi, BYTE PTR [edi+15]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+12]
	movzx edi, BYTE PTR [edi+13]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+10]
	movzx edi, BYTE PTR [edi+11]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+8]
	movzx edi, BYTE PTR [edi+9]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	shr esi, 5
	ror edx, 21
	or edx, esi
	and edx, 65535
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	sub edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+6]
	movzx edi, BYTE PTR [edi+7]
	ror edi, 24
	or esi, edi
	sub edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	shr esi, 3
	ror ecx, 19
	or ecx, esi
	and ecx, 65535
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	sub ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+4]
	movzx edi, BYTE PTR [edi+5]
	ror edi, 24
	or esi, edi
	sub ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	shr esi, 2
	ror ebx, 18
	or ebx, esi
	and ebx, 65535
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	sub ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+2]
	movzx edi, BYTE PTR [edi+3]
	ror edi, 24
	or esi, edi
	sub ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	shr esi, 1
	ror eax, 17
	or eax, esi
	and eax, 65535
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	sub eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi]
	movzx edi, BYTE PTR [edi+1]
	ror edi, 24
	or esi, edi
	sub eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov edi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebp+64]
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	mov eax, DWORD PTR [ebp+68]
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	mov eax, DWORD PTR [ebp+72]
	mov BYTE PTR [edi+4], al
	shr eax, 8
	mov BYTE PTR [edi+5], al
	mov eax, DWORD PTR [ebp+76]
	mov BYTE PTR [edi+6], al
	shr eax, 8
	mov BYTE PTR [edi+7], al
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov ecx, DWORD PTR [eax+16]
	ret
	.p2align 6
