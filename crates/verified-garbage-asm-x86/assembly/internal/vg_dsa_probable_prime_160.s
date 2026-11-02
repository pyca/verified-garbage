// The functions of `src/internal/vg_dsa_probable_prime_160.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_probable_prime_160:
	push ebx
	push ebp
	push esi
	push edi
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [edi+44], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov esi, edi
	add esi, 1600
	mov ebx, edi
	add ebx, 272
	mov ecx, 5
20:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 20b
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, 0
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov ecx, 0
	mov ebp, edi
21:
	mov eax, DWORD PTR [ebp+256]
	mov edx, DWORD PTR [ebp+256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+496], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 21b
	mov eax, DWORD PTR [edi+496]
	sub eax, 1
	mov DWORD PTR [edi+496], eax
	lea esp, [esp-20]
	add edi, 256
	mov DWORD PTR [esp], edi
	mov eax, edi
	add eax, 32
	mov DWORD PTR [esp+4], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_RSA_KEYGEN_TRIAL32}
	pop ecx
	mov DWORD PTR [esp+8], eax
	mov eax, 512
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
22:
	mov edx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov edi, DWORD PTR [esp]
	mov ebp, 0
23:
	mov eax, DWORD PTR [edi]
	add eax, ebp
	mov ebp, 0
	adc ebp, 0
	mov ecx, eax
	mul esi
	mul ebx
	add eax, ecx
	adc edx, ebp
	mov ebp, edx
	add edi, 4
	cmp edi, DWORD PTR [esp+4]
	jne 23b
	mov eax, 0
	mov edx, ebp
	sub edx, 1
	adc eax, 0
	sub ebp, ebx
	sub ebp, 1
	adc eax, 0
	mov DWORD PTR [esp+16], eax
	mov ecx, eax
	sub ecx, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 8
	mov DWORD PTR [esp+8], edx
	mov eax, DWORD PTR [esp+12]
	sub eax, 1
	and eax, ecx
	mov DWORD PTR [esp+12], eax
	cmp eax, 0
	jne 22b
	mov eax, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp]
	sub edi, 256
	lea esp, [esp+20]
	cmp eax, 0
	jne 24f
	mov edx, DWORD PTR [edi+40]
	lea esp, [esp-28]
	mov DWORD PTR [esp+24], edx
	mov edx, 0
	mov eax, 4
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], edx
	mov eax, 48
	mov DWORD PTR [edi+224], eax
	mov DWORD PTR [edi+228], edx
	mov eax, edi
	add eax, 256
	mov DWORD PTR [edi+64], eax
	mov DWORD PTR [edi+68], edx
	mov eax, edi
	add eax, 304
	mov DWORD PTR [edi+72], eax
	mov DWORD PTR [edi+76], edx
	mov eax, edi
	add eax, 352
	mov DWORD PTR [edi+80], eax
	mov DWORD PTR [edi+84], edx
	mov eax, edi
	add eax, 400
	mov DWORD PTR [edi+88], eax
	mov DWORD PTR [edi+92], edx
	mov eax, edi
	add eax, 448
	mov DWORD PTR [edi+96], eax
	mov DWORD PTR [edi+100], edx
	mov eax, edi
	add eax, 496
	mov DWORD PTR [edi+104], eax
	mov DWORD PTR [edi+108], edx
	mov eax, edi
	add eax, 544
	mov DWORD PTR [edi+112], eax
	mov DWORD PTR [edi+116], edx
	mov eax, edi
	add eax, 592
	mov DWORD PTR [edi+120], eax
	mov DWORD PTR [edi+124], edx
	mov ebx, DWORD PTR [edi+256]
	mov ecx, ebx
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+56], eax
	mov ebx, DWORD PTR [edi+256]
	mov esi, DWORD PTR [edi+260]
	mov ecx, DWORD PTR [edi+56]
	mov eax, ebx
	mul ecx
	add eax, 1
	adc edx, 0
	mov ebp, edx
	mov eax, esi
	mul ecx
	add eax, ebp
	mov ebp, eax
	mov eax, ecx
	mul ebp
	mov DWORD PTR [edi+60], eax
	mov eax, 0
	mov ebp, edi
26:
	mov DWORD PTR [ebp+544], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 26b
	mov eax, -2147483648
	mov DWORD PTR [edi+560], eax
	mov esi, 101
27:
	mov ecx, 0
	mov ebp, edi
28:
	mov eax, DWORD PTR [ebp+544]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+544]
	mov DWORD PTR [ebp+352], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 28b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+384], eax
	mov ecx, 0
	mov ebp, edi
29:
	mov eax, DWORD PTR [ebp+352]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+304], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 29b
	mov eax, DWORD PTR [edi+384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
210:
	mov eax, DWORD PTR [ebp+352]
	mov edx, DWORD PTR [ebp+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+544], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 210b
	sub esi, 1
	cmp esi, 0
	jne 27b
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 6
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [edi+96]
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
211:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 211b
	mov eax, 0
	mov ebp, edi
212:
	mov DWORD PTR [ebp+544], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 212b
	mov eax, 1
	mov DWORD PTR [edi+544], eax
	mov eax, 4
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
213:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 213b
	mov ecx, 0
	mov ebp, edi
214:
	mov eax, DWORD PTR [ebp+256]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+688]
	mov DWORD PTR [ebp+736], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 214b
	mov ebx, 0
	mov esi, 0
	mov eax, DWORD PTR [edi+496]
	mov ecx, DWORD PTR [edi+500]
	mov edx, ebx
	or edx, esi
	cmp edx, 1
	sbb edx, edx
	and eax, edx
	and ecx, edx
	or ebx, eax
	or esi, ecx
	mov eax, DWORD PTR [edi+504]
	mov ecx, DWORD PTR [edi+508]
	mov edx, ebx
	or edx, esi
	cmp edx, 1
	sbb edx, edx
	and eax, edx
	and ecx, edx
	or ebx, eax
	or esi, ecx
	mov eax, DWORD PTR [edi+512]
	mov ecx, DWORD PTR [edi+516]
	mov edx, ebx
	or edx, esi
	cmp edx, 1
	sbb edx, edx
	and eax, edx
	and ecx, edx
	or ebx, eax
	or esi, ecx
	mov eax, DWORD PTR [edi+520]
	mov ecx, DWORD PTR [edi+524]
	mov edx, ebx
	or edx, esi
	cmp edx, 1
	sbb edx, edx
	and eax, edx
	and ecx, edx
	or ebx, eax
	or esi, ecx
	mov eax, 0
	sub eax, ebx
	mov edx, 0
	sbb edx, esi
	and eax, ebx
	and edx, esi
	mov DWORD PTR [edi+136], eax
	mov DWORD PTR [edi+140], edx
	mov eax, 0
	mov DWORD PTR [edi+288], eax
	mov DWORD PTR [edi+1584], eax
	mov ecx, -1
	mov ebp, edi
215:
	mov eax, DWORD PTR [ebp+260]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+256]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp+256]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+1552], ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 215b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, -572662307
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov ebp, edi
216:
	mov eax, DWORD PTR [ebp+1556]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+1552]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp+1552]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+1552], ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 216b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, -1717986919
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov ebp, edi
217:
	mov eax, DWORD PTR [ebp+1556]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+1552]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp+1552]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+1552], ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 217b
	mov eax, DWORD PTR [edi+136]
	or eax, DWORD PTR [edi+140]
	and eax, 286331153
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov ebp, edi
218:
	mov eax, DWORD PTR [ebp+1556]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+1552]
	shr edx, 1
	add edx, eax
	mov ebx, DWORD PTR [ebp+1552]
	xor edx, ebx
	and edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+1552], ebx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 218b
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+140]
	mov DWORD PTR [edi+1584], eax
	mov DWORD PTR [edi+1588], edx
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov DWORD PTR [edi+192], eax
	mov eax, 64
	mov DWORD PTR [edi+200], eax
219:
	mov eax, DWORD PTR [edi+32]
	sub eax, DWORD PTR [edi+152]
	cmp eax, 24
	jb 220f
	mov esi, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+152]
	add esi, eax
	add eax, 24
	mov DWORD PTR [edi+152], eax
	mov ebx, edi
	add ebx, 564
	mov ecx, 6
222:
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [ebx], eax
	add esi, 4
	sub ebx, 4
	sub ecx, 1
	jne 222b
	mov eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, 0
	mov DWORD PTR [edi+568], eax
	mov eax, 0
	mov DWORD PTR [edi+572], eax
	mov ebx, 0
	mov ebp, edi
223:
	or ebx, DWORD PTR [ebp+548]
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 223b
	mov eax, DWORD PTR [edi+544]
	or eax, 1
	xor eax, 1
	or ebx, eax
	cmp ebx, 1
	sbb ebx, ebx
	xor ebx, -1
	mov esi, DWORD PTR [edi+544]
	mov eax, esi
	or eax, 1
	mov DWORD PTR [edi+544], eax
	mov ecx, 0
	mov ebp, edi
224:
	mov eax, DWORD PTR [ebp+544]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+256]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 224b
	mov eax, ecx
	mov DWORD PTR [edi+544], esi
	and eax, ebx
	mov ecx, eax
	xor ecx, -1
	and ecx, 2
	or ecx, DWORD PTR [edi+544]
	mov DWORD PTR [edi+544], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, -2147483648
	xor ecx, -1
	and ecx, DWORD PTR [edi+560]
	mov DWORD PTR [edi+560], ecx
	mov DWORD PTR [edi+144], eax
	mov eax, 4
	mov ecx, 6
	mov edx, DWORD PTR [esp+24]
	push eax
	push ecx
	push ecx
	push edx
	push edi
	call {vg_rsa_mont_mul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [edi+104]
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
225:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 225b
	mov edx, DWORD PTR [esp+24]
	push edx
	push edi
	call {vg_miller_rabin_round}
	pop ecx
	pop ecx
	mov esi, eax
	mov eax, DWORD PTR [edi+176]
	add eax, 1
	mov DWORD PTR [edi+176], eax
	mov ebx, DWORD PTR [edi+144]
	and ebx, 1
	add ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov edx, DWORD PTR [edi+200]
	cmp eax, 16
	sbb ecx, ecx
	cmp ebx, edx
	sbb edx, edx
	or ecx, edx
	and ecx, 3
	add ecx, 1
	mov ebp, 0
	sub ebp, esi
	and ecx, ebp
	xor ebp, -1
	and ebp, 3
	or ecx, ebp
	mov DWORD PTR [edi+168], ecx
	jmp 221f
220:
	mov eax, 0
	mov DWORD PTR [edi+168], eax
221:
	mov eax, DWORD PTR [edi+168]
	cmp eax, 4
	je 219b
	lea esp, [esp+28]
	mov eax, DWORD PTR [edi+168]
	cmp eax, 1
	je 226f
	cmp eax, 0
	je 228f
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 2
	jmp 229f
228:
	mov edx, DWORD PTR [edi+44]
	mov eax, 0
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
229:
	jmp 227f
226:
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 1
227:
	jmp 25f
24:
	mov edx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx], eax
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov eax, 2
25:
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
