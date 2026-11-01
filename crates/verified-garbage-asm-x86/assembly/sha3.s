// The functions of `src/sha3.rs` of `verified-garbage-asm-x86`, as text: generated from
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+128]
	xor eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+132]
	xor eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [esi+136]
	xor eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [esi+140]
	xor eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [esi+144]
	xor eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [esi+148]
	xor eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [esi+152]
	xor eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [esi+156]
	xor eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+416]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+440]
	xor edx, DWORD PTR [edi+444]
	mov DWORD PTR [edi+448], eax
	mov DWORD PTR [edi+452], edx
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+424]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+408]
	xor edx, DWORD PTR [edi+412]
	mov DWORD PTR [edi+456], eax
	mov DWORD PTR [edi+460], edx
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+432]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+416]
	xor edx, DWORD PTR [edi+420]
	mov DWORD PTR [edi+464], eax
	mov DWORD PTR [edi+468], edx
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+440]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+424]
	xor edx, DWORD PTR [edi+428]
	mov DWORD PTR [edi+472], eax
	mov DWORD PTR [edi+476], edx
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+408]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+432]
	xor edx, DWORD PTR [edi+436]
	mov DWORD PTR [edi+480], eax
	mov DWORD PTR [edi+484], edx
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [esi+48]
	mov edx, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+456]
	xor edx, DWORD PTR [edi+460]
	ror eax, 20
	ror edx, 20
	mov ecx, eax
	xor ecx, edx
	and ecx, -4096
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [esi+96]
	mov edx, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 21
	ror edx, 21
	mov ecx, eax
	xor ecx, edx
	and ecx, -2048
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [esi+148]
	mov edx, DWORD PTR [esi+144]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 11
	ror edx, 11
	mov ecx, eax
	xor ecx, edx
	and ecx, -2097152
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [esi+196]
	mov edx, DWORD PTR [esi+192]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 18
	ror edx, 18
	mov ecx, eax
	xor ecx, edx
	and ecx, -16384
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [ebp+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [esi+28]
	mov edx, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 4
	ror edx, 4
	mov ecx, eax
	xor ecx, edx
	and ecx, -268435456
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [esi+76]
	mov edx, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 12
	ror edx, 12
	mov ecx, eax
	xor ecx, edx
	and ecx, -1048576
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [esi+84]
	mov edx, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+452]
	xor edx, DWORD PTR [edi+448]
	ror eax, 29
	ror edx, 29
	mov ecx, eax
	xor ecx, edx
	and ecx, -8
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [esi+128]
	mov edx, DWORD PTR [esi+132]
	xor eax, DWORD PTR [edi+456]
	xor edx, DWORD PTR [edi+460]
	ror eax, 19
	ror edx, 19
	mov ecx, eax
	xor ecx, edx
	and ecx, -8192
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 3
	ror edx, 3
	mov ecx, eax
	xor ecx, edx
	and ecx, -536870912
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esi+12]
	mov edx, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [esi+60]
	mov edx, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+468]
	xor edx, DWORD PTR [edi+464]
	ror eax, 26
	ror edx, 26
	mov ecx, eax
	xor ecx, edx
	and ecx, -64
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [esi+108]
	mov edx, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 7
	ror edx, 7
	mov ecx, eax
	xor ecx, edx
	and ecx, -33554432
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [esi+156]
	mov edx, DWORD PTR [esi+152]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, -256
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [esi+164]
	mov edx, DWORD PTR [esi+160]
	xor eax, DWORD PTR [edi+452]
	xor edx, DWORD PTR [edi+448]
	ror eax, 14
	ror edx, 14
	mov ecx, eax
	xor ecx, edx
	and ecx, -262144
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 5
	ror edx, 5
	mov ecx, eax
	xor ecx, edx
	and ecx, -134217728
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	ror eax, 28
	ror edx, 28
	mov ecx, eax
	xor ecx, edx
	and ecx, -16
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [esi+92]
	mov edx, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 22
	ror edx, 22
	mov ecx, eax
	xor ecx, edx
	and ecx, -1024
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [esi+140]
	mov edx, DWORD PTR [esi+136]
	xor eax, DWORD PTR [edi+468]
	xor edx, DWORD PTR [edi+464]
	ror eax, 17
	ror edx, 17
	mov ecx, eax
	xor ecx, edx
	and ecx, -32768
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor eax, DWORD PTR [edi+472]
	xor edx, DWORD PTR [edi+476]
	ror eax, 8
	ror edx, 8
	mov ecx, eax
	xor ecx, edx
	and ecx, -16777216
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [esi+16]
	mov edx, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 2
	ror edx, 2
	mov ecx, eax
	xor ecx, edx
	and ecx, -1073741824
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+472]
	xor edx, DWORD PTR [edi+476]
	ror eax, 9
	ror edx, 9
	mov ecx, eax
	xor ecx, edx
	and ecx, -8388608
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [esi+112]
	mov edx, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+480]
	xor edx, DWORD PTR [edi+484]
	ror eax, 25
	ror edx, 25
	mov ecx, eax
	xor ecx, edx
	and ecx, -128
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [esi+120]
	mov edx, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	ror eax, 23
	ror edx, 23
	mov ecx, eax
	xor ecx, edx
	and ecx, -512
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [esi+172]
	mov edx, DWORD PTR [esi+168]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 30
	ror edx, 30
	mov ecx, eax
	xor ecx, edx
	and ecx, -4
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+196], eax
	add ebp, 8
	mov eax, DWORD PTR [edi]
	xor eax, DWORD PTR [edi+40]
	xor eax, DWORD PTR [edi+80]
	xor eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+4]
	xor eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+84]
	xor eax, DWORD PTR [edi+124]
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+128]
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+12]
	xor eax, DWORD PTR [edi+52]
	xor eax, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+132]
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+56]
	xor eax, DWORD PTR [edi+96]
	xor eax, DWORD PTR [edi+136]
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+60]
	xor eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+140]
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+64]
	xor eax, DWORD PTR [edi+104]
	xor eax, DWORD PTR [edi+144]
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+108]
	xor eax, DWORD PTR [edi+148]
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+32]
	xor eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+152]
	xor eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, DWORD PTR [edi+76]
	xor eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+156]
	xor eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+416]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+440]
	xor edx, DWORD PTR [edi+444]
	mov DWORD PTR [edi+448], eax
	mov DWORD PTR [edi+452], edx
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+424]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+408]
	xor edx, DWORD PTR [edi+412]
	mov DWORD PTR [edi+456], eax
	mov DWORD PTR [edi+460], edx
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+432]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+416]
	xor edx, DWORD PTR [edi+420]
	mov DWORD PTR [edi+464], eax
	mov DWORD PTR [edi+468], edx
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+440]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+424]
	xor edx, DWORD PTR [edi+428]
	mov DWORD PTR [edi+472], eax
	mov DWORD PTR [edi+476], edx
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+408]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	xor eax, DWORD PTR [edi+432]
	xor edx, DWORD PTR [edi+436]
	mov DWORD PTR [edi+480], eax
	mov DWORD PTR [edi+484], edx
	mov eax, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+4]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+52]
	xor eax, DWORD PTR [edi+456]
	xor edx, DWORD PTR [edi+460]
	ror eax, 20
	ror edx, 20
	mov ecx, eax
	xor ecx, edx
	and ecx, -4096
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 21
	ror edx, 21
	mov ecx, eax
	xor ecx, edx
	and ecx, -2048
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+144]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 11
	ror edx, 11
	mov ecx, eax
	xor ecx, edx
	and ecx, -2097152
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 18
	ror edx, 18
	mov ecx, eax
	xor ecx, edx
	and ecx, -16384
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [ebp+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 4
	ror edx, 4
	mov ecx, eax
	xor ecx, edx
	and ecx, -268435456
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 12
	ror edx, 12
	mov ecx, eax
	xor ecx, edx
	and ecx, -1048576
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+80]
	xor eax, DWORD PTR [edi+452]
	xor edx, DWORD PTR [edi+448]
	ror eax, 29
	ror edx, 29
	mov ecx, eax
	xor ecx, edx
	and ecx, -8
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+132]
	xor eax, DWORD PTR [edi+456]
	xor edx, DWORD PTR [edi+460]
	ror eax, 19
	ror edx, 19
	mov ecx, eax
	xor ecx, edx
	and ecx, -8192
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 3
	ror edx, 3
	mov ecx, eax
	xor ecx, edx
	and ecx, -536870912
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 31
	ror edx, 31
	mov ecx, eax
	xor ecx, edx
	and ecx, -2
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+56]
	xor eax, DWORD PTR [edi+468]
	xor edx, DWORD PTR [edi+464]
	ror eax, 26
	ror edx, 26
	mov ecx, eax
	xor ecx, edx
	and ecx, -64
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+104]
	xor eax, DWORD PTR [edi+476]
	xor edx, DWORD PTR [edi+472]
	ror eax, 7
	ror edx, 7
	mov ecx, eax
	xor ecx, edx
	and ecx, -33554432
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+152]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 24
	ror edx, 24
	mov ecx, eax
	xor ecx, edx
	and ecx, -256
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+452]
	xor edx, DWORD PTR [edi+448]
	ror eax, 14
	ror edx, 14
	mov ecx, eax
	xor ecx, edx
	and ecx, -262144
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+32]
	xor eax, DWORD PTR [edi+484]
	xor edx, DWORD PTR [edi+480]
	ror eax, 5
	ror edx, 5
	mov ecx, eax
	xor ecx, edx
	and ecx, -134217728
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	ror eax, 28
	ror edx, 28
	mov ecx, eax
	xor ecx, edx
	and ecx, -16
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 22
	ror edx, 22
	mov ecx, eax
	xor ecx, edx
	and ecx, -1024
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+136]
	xor eax, DWORD PTR [edi+468]
	xor edx, DWORD PTR [edi+464]
	ror eax, 17
	ror edx, 17
	mov ecx, eax
	xor ecx, edx
	and ecx, -32768
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+188]
	xor eax, DWORD PTR [edi+472]
	xor edx, DWORD PTR [edi+476]
	ror eax, 8
	ror edx, 8
	mov ecx, eax
	xor ecx, edx
	and ecx, -16777216
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+464]
	xor edx, DWORD PTR [edi+468]
	ror eax, 2
	ror edx, 2
	mov ecx, eax
	xor ecx, edx
	and ecx, -1073741824
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+408], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+472]
	xor edx, DWORD PTR [edi+476]
	ror eax, 9
	ror edx, 9
	mov ecx, eax
	xor ecx, edx
	and ecx, -8388608
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+416], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+480]
	xor edx, DWORD PTR [edi+484]
	ror eax, 25
	ror edx, 25
	mov ecx, eax
	xor ecx, edx
	and ecx, -128
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+424], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+124]
	xor eax, DWORD PTR [edi+448]
	xor edx, DWORD PTR [edi+452]
	ror eax, 23
	ror edx, 23
	mov ecx, eax
	xor ecx, edx
	and ecx, -512
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+432], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+460]
	xor edx, DWORD PTR [edi+456]
	ror eax, 30
	ror edx, 30
	mov ecx, eax
	xor ecx, edx
	and ecx, -4
	xor eax, ecx
	xor edx, ecx
	mov DWORD PTR [edi+440], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	and eax, DWORD PTR [edi+424]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	and eax, DWORD PTR [edi+428]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	and eax, DWORD PTR [edi+432]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	and eax, DWORD PTR [edi+436]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	and eax, DWORD PTR [edi+440]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	and eax, DWORD PTR [edi+444]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	and eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	and eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	and eax, DWORD PTR [edi+416]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	and eax, DWORD PTR [edi+420]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+196], eax
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

vg_keccak_absorb:
	lea esp, [esp-668]
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ecx]
	mov BYTE PTR [ecx], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	test edi, edi
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	lea esp, [esp+668]
	ret
	.p2align 6

vg_keccak_absorb_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ecx]
	mov BYTE PTR [ecx], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	test edi, edi
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	ret
	.p2align 6

vg_keccak_pad:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	add edx, ecx
	movzx ebx, BYTE PTR [edx]
	xor ebx, DWORD PTR [esp+16]
	mov BYTE PTR [edx], bl
	mov edx, ecx
	add edx, eax
	sub edx, 1
	movzx ebx, BYTE PTR [edx]
	xor ebx, 128
	mov BYTE PTR [edx], bl
	push esi
	push ecx
	call {vg_keccak_f1600}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esi+512]
	mov esi, DWORD PTR [esi+516]
	lea esp, [esp+664]
	ret
	.p2align 6

vg_keccak_pad_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	add edx, ecx
	movzx ebx, BYTE PTR [edx]
	xor ebx, DWORD PTR [esp+16]
	mov BYTE PTR [edx], bl
	mov edx, ecx
	add edx, eax
	sub edx, 1
	movzx ebx, BYTE PTR [edx]
	xor ebx, 128
	mov BYTE PTR [edx], bl
	push esi
	push ecx
	call {vg_keccak_f1600}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esi+512]
	mov esi, DWORD PTR [esi+516]
	ret
	.p2align 6

vg_keccak_squeeze:
	lea esp, [esp-668]
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [esi], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	lea esp, [esp+668]
	ret
	.p2align 6

vg_keccak_squeeze_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [esi], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	ret
	.p2align 6
