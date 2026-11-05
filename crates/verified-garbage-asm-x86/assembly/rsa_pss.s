// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_verify_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov edx, DWORD PTR [esp+220]
	mov edx, DWORD PTR [edx+20]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 214f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
216:
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
217:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 217b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 216b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
218:
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
	jne 218b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 219f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
221:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 221b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
222:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 222b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+48]
223:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 223b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
224:
	mov esi, ebp
	add esi, 2088
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
225:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 224b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 39
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 55
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
226:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 226b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
227:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 227b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
228:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
229:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 229b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
230:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 230b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 228b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 32
231:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 231b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 220f
219:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
232:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 232b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
233:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 233b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 234f
236:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 236b
	jmp 235f
234:
235:
	mov eax, DWORD PTR [esp+196]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
237:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 237b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
238:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 238b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
239:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
240:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 240b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
241:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 241b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 239b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 32
242:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 242b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
220:
	jmp 215f
214:
	mov eax, 0
215:
	jmp 213f
212:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 29
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 243f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
245:
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
246:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 246b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 245b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
247:
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
	jne 247b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 248f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
250:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 250b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
251:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 251b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+48]
252:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 252b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
253:
	mov esi, ebp
	add esi, 2084
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
254:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 254b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 253b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 35
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 51
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
255:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 255b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
256:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 256b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
257:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
258:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 258b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
259:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 259b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 257b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 28
260:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 260b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 249f
248:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
261:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 261b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
262:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 262b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 263f
265:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 265b
	jmp 264f
263:
264:
	mov eax, DWORD PTR [esp+196]
	add eax, 36
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
266:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 266b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
267:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 267b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
268:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
269:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 269b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
270:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 270b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 268b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 28
271:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 271b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
249:
	jmp 244f
243:
	mov eax, 0
244:
213:
	jmp 211f
210:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 65
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 272f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 64
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
274:
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
275:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 275b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 274b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
276:
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
	jne 276b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 277f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
279:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 279b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 64
280:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 280b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2120
	mov ecx, DWORD PTR [esp+48]
281:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 281b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
282:
	mov esi, ebp
	add esi, 2120
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
283:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 283b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 282b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 71
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 87
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
284:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 284b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
285:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 285b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
286:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
287:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 287b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
288:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 288b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 286b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 64
289:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 289b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 278f
277:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
290:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 290b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 64
291:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 291b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2120
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 292f
294:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 294b
	jmp 293f
292:
293:
	mov eax, DWORD PTR [esp+196]
	add eax, 72
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
295:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 295b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
296:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 296b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
297:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
298:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 298b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
299:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 299b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 297b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 64
2100:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2100b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
278:
	jmp 273f
272:
	mov eax, 0
273:
211:
	jmp 29f
28:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 49
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2101f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 48
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2103:
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
2104:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2104b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2103b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
2105:
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
	jne 2105b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 2106f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2108:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2108b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 48
2109:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2109b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2104
	mov ecx, DWORD PTR [esp+48]
2110:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2110b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
2111:
	mov esi, ebp
	add esi, 2104
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
2112:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2112b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 2111b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 55
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 71
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
2113:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2113b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2114:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2114b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2115:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
2116:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2116b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
2117:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2117b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2115b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 48
2118:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2118b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 2107f
2106:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2119:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2119b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 48
2120:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2120b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2104
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 2121f
2123:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2123b
	jmp 2122f
2121:
2122:
	mov eax, DWORD PTR [esp+196]
	add eax, 56
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
2124:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2124b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2125:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2125b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2126:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
2127:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2127b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
2128:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2128b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2126b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 48
2129:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2129b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
2107:
	jmp 2102f
2101:
	mov eax, 0
2102:
29:
	jmp 27f
26:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2130f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2132:
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
2133:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2133b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2132b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
2134:
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
	jne 2134b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 2135f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2137:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2137b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
2138:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2138b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+48]
2139:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2139b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
2140:
	mov esi, ebp
	add esi, 2088
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
2141:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2141b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 2140b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 39
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 47
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2142:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2142b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2143:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2143b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2144:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2145:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2145b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2146:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2146b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2144b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 32
2147:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2147b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 2136f
2135:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2148:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2148b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
2149:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2149b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 2150f
2152:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2152b
	jmp 2151f
2150:
2151:
	mov eax, DWORD PTR [esp+196]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2153:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2153b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2154:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2154b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2155:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2156:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2156b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2157:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2157b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2155b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 32
2158:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2158b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
2136:
	jmp 2131f
2130:
	mov eax, 0
2131:
27:
	jmp 25f
24:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 29
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2159f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2161:
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
2162:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2162b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2161b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
2163:
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
	jne 2163b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 2164f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2166:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2166b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
2167:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2167b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+48]
2168:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2168b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
2169:
	mov esi, ebp
	add esi, 2084
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
2170:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2170b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 2169b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 35
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 43
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2171:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2171b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2172:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2172b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2173:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2174:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2174b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2175:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2175b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2173b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 28
2176:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2176b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 2165f
2164:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2177:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2177b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
2178:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2178b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 2179f
2181:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2181b
	jmp 2180f
2179:
2180:
	mov eax, DWORD PTR [esp+196]
	add eax, 36
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2182:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2182b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2183:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2183b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2184:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2185:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2185b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2186:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2186b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2184b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 28
2187:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2187b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
2165:
	jmp 2160f
2159:
	mov eax, 0
2160:
25:
	jmp 23f
22:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 21
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2188f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 20
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2190:
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
2191:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2191b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2190b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
2192:
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
	jne 2192b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 2193f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2195:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2195b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 20
2196:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2196b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2076
	mov ecx, DWORD PTR [esp+48]
2197:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2197b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
2198:
	mov esi, ebp
	add esi, 2076
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
2199:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2199b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 2198b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 27
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 35
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2200:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2200b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2201:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2201b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2202:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 532
	mov ecx, 64
2203:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2203b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 532
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 20
2204:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2204b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2202b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 20
2205:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2205b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 2194f
2193:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2206:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2206b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 20
2207:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2207b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2076
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 2208f
2210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2210b
	jmp 2209f
2208:
2209:
	mov eax, DWORD PTR [esp+196]
	add eax, 28
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2211:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2211b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2212:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2212b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2213:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 532
	mov ecx, 64
2214:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2214b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 532
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 20
2215:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2215b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2213b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 20
2216:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2216b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
2194:
	jmp 2189f
2188:
	mov eax, 0
2189:
23:
	jmp 21f
20:
	mov ebp, DWORD PTR [esp+204]
	mov edx, DWORD PTR [esp+196]
	mov edi, DWORD PTR [esp+200]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+52], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 17
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2217f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+208]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+40]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+44]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 16
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2219:
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
2220:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2220b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2219b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ecx, DWORD PTR [esp+48]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
2221:
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
	jne 2221b
	mov ebp, DWORD PTR [esp+204]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+48]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+52]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+52]
	test eax, eax
	je 2222f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2224:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2224b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 16
2225:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2225b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	mov ebx, ebp
	add ebx, 2072
	mov ecx, DWORD PTR [esp+48]
2226:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2226b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
2227:
	mov esi, ebp
	add esi, 2072
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+48]
2228:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2228b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 2227b
	mov eax, DWORD PTR [esp+48]
	sub eax, DWORD PTR [esp+116]
	add eax, 23
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+48]
	add eax, 31
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2229:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2229b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebx+56], eax
	mov DWORD PTR [ebx+60], ecx
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2230:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2230b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2231:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 528
	mov ecx, 64
2232:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2232b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 528
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 16
2233:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2233b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2231b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 16
2234:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2234b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 2223f
2222:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2235:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2235b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 16
2236:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2236b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	add esi, DWORD PTR [esp+48]
	sub esi, DWORD PTR [esp+196]
	mov ebx, ebp
	add ebx, 2072
	mov ecx, DWORD PTR [esp+196]
	test ecx, ecx
	je 2237f
2239:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2239b
	jmp 2238f
2237:
2238:
	mov eax, DWORD PTR [esp+196]
	add eax, 24
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2240:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2240b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebx+56], eax
	mov DWORD PTR [ebx+60], ecx
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2241:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2241b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2242:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 528
	mov ecx, 64
2243:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2243b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 528
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 16
2244:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2244b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2242b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+40]
	add edi, DWORD PTR [esp+48]
	mov edx, 0
	mov ecx, 16
2245:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2245b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
2223:
	jmp 2218f
2217:
	mov eax, 0
2218:
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

vg_rsa_pss_sign:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov edx, DWORD PTR [esp+252]
	mov edx, DWORD PTR [edx+20]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 214f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
216:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 216b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 218f
220:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 220b
	jmp 219f
218:
219:
	mov eax, DWORD PTR [esp+240]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
221:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 221b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
222:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 222b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
223:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
224:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 224b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
225:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 223b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
226:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 226b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 227f
229:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 229b
	jmp 228f
227:
228:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 32
230:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 230b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
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
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 215f
214:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
233:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 233b
	mov eax, 0
215:
	jmp 213f
212:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 29
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 234f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
236:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 236b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
237:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 237b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 238f
240:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 240b
	jmp 239f
238:
239:
	mov eax, DWORD PTR [esp+240]
	add eax, 36
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
241:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 241b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
242:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 242b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
243:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
244:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 244b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
245:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 245b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 243b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
246:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 246b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 247f
249:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 249b
	jmp 248f
247:
248:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 28
250:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 250b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
251:
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
252:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 252b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 251b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 235f
234:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
253:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 253b
	mov eax, 0
235:
213:
	jmp 211f
210:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 65
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 254f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
256:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 256b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 64
257:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 257b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2120
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 258f
260:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 260b
	jmp 259f
258:
259:
	mov eax, DWORD PTR [esp+240]
	add eax, 72
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
261:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 261b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
262:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 262b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
263:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
264:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 264b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
265:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 265b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 263b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
266:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 266b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
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
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 64
270:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 270b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 64
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
271:
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
272:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 272b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 271b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 255f
254:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
273:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 273b
	mov eax, 0
255:
211:
	jmp 29f
28:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 49
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 274f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
276:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 276b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 48
277:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 277b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2104
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 278f
280:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 280b
	jmp 279f
278:
279:
	mov eax, DWORD PTR [esp+240]
	add eax, 56
	mov DWORD PTR [esp+92], eax
	add eax, 16
	shr eax, 7
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 128
	mov eax, 0
281:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 281b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+120], ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 16
	shr eax, 7
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
282:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 7
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 127
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 282b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
283:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 576
	mov ecx, 128
284:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 284b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 576
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 64
285:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 285b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 283b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
286:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 286b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 287f
289:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 289b
	jmp 288f
287:
288:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 48
290:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 290b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 48
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
291:
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
292:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 292b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 291b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 275f
274:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
293:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 293b
	mov eax, 0
275:
29:
	jmp 27f
26:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 294f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
296:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 296b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
297:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 297b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 298f
2100:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2100b
	jmp 299f
298:
299:
	mov eax, DWORD PTR [esp+240]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2101:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2101b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2102:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2102b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2103:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2104:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2104b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2105:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2105b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2103b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2106:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2106b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2107f
2109:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2109b
	jmp 2108f
2107:
2108:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 32
2110:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2110b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 32
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2111:
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
2112:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2112b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2111b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 295f
294:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2113:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2113b
	mov eax, 0
295:
27:
	jmp 25f
24:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 29
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2114f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2116:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2116b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 28
2117:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2117b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2084
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2118f
2120:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2120b
	jmp 2119f
2118:
2119:
	mov eax, DWORD PTR [esp+240]
	add eax, 36
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2121:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2121b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2122:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2122b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2123:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
2124:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2124b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
2125:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2125b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2123b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2126:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2126b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2127f
2129:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2129b
	jmp 2128f
2127:
2128:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 28
2130:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2130b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2131:
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
2132:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2132b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2131b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 2115f
2114:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2133:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2133b
	mov eax, 0
2115:
25:
	jmp 23f
22:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 21
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2134f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2136:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2136b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 20
2137:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2137b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2076
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2138f
2140:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2140b
	jmp 2139f
2138:
2139:
	mov eax, DWORD PTR [esp+240]
	add eax, 28
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2141:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2141b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2142:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2142b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2143:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 532
	mov ecx, 64
2144:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2144b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 532
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 20
2145:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2145b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2143b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2146:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2146b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2147f
2149:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2149b
	jmp 2148f
2147:
2148:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 20
2150:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2150b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 20
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2151:
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
2152:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2152b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2151b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 2135f
2134:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2153:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2153b
	mov eax, 0
2135:
23:
	jmp 21f
20:
	mov ebp, DWORD PTR [esp+244]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+240]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+40], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+44], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 17
	mov DWORD PTR [esp+48], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 2154f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
2156:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2156b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 16
2157:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2157b
	mov esi, DWORD PTR [esp+236]
	mov ebx, ebp
	add ebx, 2072
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2158f
2160:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2160b
	jmp 2159f
2158:
2159:
	mov eax, DWORD PTR [esp+240]
	add eax, 24
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+132], eax
	mov ebx, ebp
	add ebx, 512
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
2161:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2161b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebx+56], eax
	mov DWORD PTR [ebx+60], ecx
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
2162:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 2162b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
2163:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 528
	mov ecx, 64
2164:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2164b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 528
	mov ecx, 1
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+12]
	push ebp
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 16
2165:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 2165b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 2163b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov esi, DWORD PTR [esp+132]
	mov esi, DWORD PTR [esi+16]
	push ebx
	call esi
	pop eax
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2166:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2166b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	sub ebx, DWORD PTR [esp+240]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+240]
	test ecx, ecx
	je 2167f
2169:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2169b
	jmp 2168f
2167:
2168:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+40]
	add ebx, DWORD PTR [esp+48]
	mov ecx, 16
2170:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2170b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, ebp
	add eax, 1024
	add eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+88], eax
	mov ecx, DWORD PTR [esp+48]
	mov DWORD PTR [esp+92], ecx
	add eax, ecx
	mov DWORD PTR [esp+80], eax
	mov eax, 16
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [esp+132], eax
	mov eax, DWORD PTR [eax+16]
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
2171:
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
2172:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 2172b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 2171b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+40]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+44]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
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
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+248]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 2155f
2154:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
2173:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2173b
	mov eax, 0
2155:
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
