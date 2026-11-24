// The functions of `src/internal/vg_ed25519_scalar_reduce.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_reduce:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+188], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, 170660635
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, -308484701
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, 140716455
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, 554049885
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, -21
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, 15
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+480], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+484], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+488], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, 350157278
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+492], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, 350157278
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+496], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, 350157278
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+500], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, 350157278
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+504], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, 268435456
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, 350157278
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, -1560830762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, 1477600026
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, 1559614445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+508], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+128]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+480]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, 1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+132]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+136]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+140]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+144]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+148]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+152]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+156]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+92], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [esi+28], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6
