// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_encrypt_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov edx, DWORD PTR [esp+228]
	mov edx, DWORD PTR [edx+16]
	cmp edx, 20
	je 20f
	cmp edx, 28
	je 22f
	cmp edx, 32
	je 24f
	cmp edx, 48
	je 26f
	cmp edx, 64
	je 28f
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 34
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 210f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 16
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 213b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1041
	mov ecx, 16
214:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 214b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 215f
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
	jmp 216f
215:
216:
	mov eax, ebp
	add eax, 1041
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 17
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 16
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
218:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
219:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 218b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 16
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1041
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 17
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
220:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
221:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 221b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 220b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 211f
210:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
222:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 222b
	mov eax, 0
211:
	jmp 29f
28:
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 130
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 223f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
225:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 225b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 64
226:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 226b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1089
	mov ecx, 64
227:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 227b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 228f
230:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 230b
	jmp 229f
228:
229:
	mov eax, ebp
	add eax, 1089
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 65
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 64
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
231:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
232:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 232b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 231b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 64
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1089
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 65
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
233:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
234:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 234b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 233b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 224f
223:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
235:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 235b
	mov eax, 0
224:
29:
	jmp 27f
26:
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 98
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 236f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
238:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 238b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 48
239:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 239b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1073
	mov ecx, 48
240:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 240b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 241f
243:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 243b
	jmp 242f
241:
242:
	mov eax, ebp
	add eax, 1073
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 49
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 48
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
244:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
245:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 245b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 244b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 48
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1073
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 49
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
246:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
247:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 247b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 246b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 237f
236:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
248:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 248b
	mov eax, 0
237:
27:
	jmp 25f
24:
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 66
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 249f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
251:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 251b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 32
252:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 252b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1057
	mov ecx, 32
253:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 253b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 254f
256:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 256b
	jmp 255f
254:
255:
	mov eax, ebp
	add eax, 1057
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 33
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
257:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
258:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 258b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 257b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 32
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1057
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 33
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
259:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
260:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 260b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 259b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 250f
249:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
261:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 261b
	mov eax, 0
250:
25:
	jmp 23f
22:
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 58
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 262f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
264:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 264b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 28
265:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 265b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1053
	mov ecx, 28
266:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 266b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 267f
269:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 269b
	jmp 268f
267:
268:
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
270:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
271:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 271b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 270b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
272:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
273:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 273b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 272b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 263f
262:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
274:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 274b
	mov eax, 0
263:
23:
	jmp 21f
20:
	mov ebp, DWORD PTR [esp+212]
	mov eax, DWORD PTR [esp+176]
	sub eax, 42
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 275f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
277:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 277b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 20
278:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 278b
	mov edx, DWORD PTR [esp+228]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1045
	mov ecx, 20
279:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 279b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 280f
282:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 282b
	jmp 281f
280:
281:
	mov eax, ebp
	add eax, 1045
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 21
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 20
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
283:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
284:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 284b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 283b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 20
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1045
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 21
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
285:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
286:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 286b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 285b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+216]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 276f
275:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
287:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 287b
	mov eax, 0
276:
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_decrypt:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+248]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+252]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov edx, DWORD PTR [esp+256]
	mov edx, DWORD PTR [edx+16]
	cmp edx, 20
	je 20f
	cmp edx, 28
	je 22f
	cmp edx, 32
	je 24f
	cmp edx, 48
	je 26f
	cmp edx, 64
	je 28f
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 34
	jb 210f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 16
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1041
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 17
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
212:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
213:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 213b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 212b
	mov eax, ebp
	add eax, 1041
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 17
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 16
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
214:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
215:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 215b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 214b
	mov esi, ebp
	add esi, 1041
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 16
216:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 216b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1057
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 33
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
217:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 217b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
218:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 218b
	mov esi, ebp
	add esi, 1057
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 33
219:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 219b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
220:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
221:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 221b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 220b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
222:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 222b
	mov eax, DWORD PTR [esp+180]
	sub eax, 34
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 211f
210:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
223:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 223b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
211:
	jmp 29f
28:
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 130
	jb 224f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 64
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1089
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 65
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
226:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
227:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 227b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 226b
	mov eax, ebp
	add eax, 1089
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 65
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 64
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
228:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
229:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 229b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 228b
	mov esi, ebp
	add esi, 1089
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 64
230:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 230b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1153
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 129
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
231:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 231b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
232:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 232b
	mov esi, ebp
	add esi, 1153
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 129
233:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 233b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
234:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
235:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 235b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 234b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
236:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 236b
	mov eax, DWORD PTR [esp+180]
	sub eax, 130
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 225f
224:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
237:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 237b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
225:
29:
	jmp 27f
26:
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 98
	jb 238f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 48
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1073
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 49
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
240:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
241:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 241b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 240b
	mov eax, ebp
	add eax, 1073
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 49
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 48
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
242:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
243:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 243b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 242b
	mov esi, ebp
	add esi, 1073
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 48
244:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 244b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1121
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 97
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
245:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 245b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
246:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 246b
	mov esi, ebp
	add esi, 1121
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 97
247:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 247b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
248:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
249:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 249b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 248b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
250:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 250b
	mov eax, DWORD PTR [esp+180]
	sub eax, 98
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 239f
238:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
251:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 251b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
239:
27:
	jmp 25f
24:
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 66
	jb 252f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 32
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1057
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 33
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
254:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
255:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 255b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 254b
	mov eax, ebp
	add eax, 1057
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 33
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
256:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
257:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 257b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 256b
	mov esi, ebp
	add esi, 1057
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 32
258:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 258b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1089
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 65
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
259:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 259b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
260:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 260b
	mov esi, ebp
	add esi, 1089
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 65
261:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 261b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
262:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
263:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 263b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 262b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
264:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 264b
	mov eax, DWORD PTR [esp+180]
	sub eax, 66
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 253f
252:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
265:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 265b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
253:
25:
	jmp 23f
22:
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 58
	jb 266f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
268:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
269:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 269b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 268b
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
270:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
271:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 271b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 270b
	mov esi, ebp
	add esi, 1053
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 28
272:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 272b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1081
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
273:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 273b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
274:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 274b
	mov esi, ebp
	add esi, 1081
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
275:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 275b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
276:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
277:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 277b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 276b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
278:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 278b
	mov eax, DWORD PTR [esp+180]
	sub eax, 58
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 267f
266:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
279:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 279b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
267:
23:
	jmp 21f
20:
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 42
	jb 280f
	mov edx, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], edx
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 20
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1045
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 21
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
282:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
283:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 283b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 282b
	mov eax, ebp
	add eax, 1045
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 21
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 20
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+260]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
284:
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, DWORD PTR [esp+136]
	sbb edx, edx
	and eax, edx
	add eax, DWORD PTR [esp+136]
	mov ecx, eax
285:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 285b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 284b
	mov esi, ebp
	add esi, 1045
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 20
286:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 286b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1065
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 41
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
287:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 287b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
288:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 288b
	mov esi, ebp
	add esi, 1065
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 41
289:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 289b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
290:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
291:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 291b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 290b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
292:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 292b
	mov eax, DWORD PTR [esp+180]
	sub eax, 42
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 281f
280:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
293:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 293b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
281:
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
