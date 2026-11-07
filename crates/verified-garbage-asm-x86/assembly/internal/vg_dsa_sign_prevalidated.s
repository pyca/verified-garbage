// The functions of `src/internal/vg_dsa_sign_prevalidated.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_prevalidated:
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+8256], ebx
	mov DWORD PTR [eax+8260], ebp
	mov DWORD PTR [eax+8264], esi
	mov DWORD PTR [eax+8268], edi
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [edi+8224], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+8192], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+8228], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+8216], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [edi+8232], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [edi+8220], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [edi+8236], eax
	mov eax, DWORD PTR [edi+8192]
	add eax, DWORD PTR [edi+8228]
	mov DWORD PTR [edi+8196], eax
	add eax, DWORD PTR [edi+8232]
	mov DWORD PTR [edi+8200], eax
	add eax, DWORD PTR [edi+8228]
	mov DWORD PTR [edi+8204], eax
	add eax, DWORD PTR [edi+8228]
	mov DWORD PTR [edi+8208], eax
	mov eax, DWORD PTR [edi+8228]
	cmp eax, 128
	je 20f
	mov eax, 0
	cmp eax, 1
	jmp 21f
20:
	mov eax, DWORD PTR [edi+8232]
	cmp eax, 20
21:
	je 22f
	mov eax, DWORD PTR [edi+8228]
	cmp eax, 256
	je 24f
	mov eax, 0
	cmp eax, 1
	jmp 25f
24:
	mov eax, DWORD PTR [edi+8232]
	cmp eax, 28
25:
	je 26f
	mov eax, DWORD PTR [edi+8228]
	cmp eax, 256
	je 28f
	mov eax, 0
	cmp eax, 1
	jmp 29f
28:
	mov eax, DWORD PTR [edi+8232]
	cmp eax, 32
29:
	je 210f
	mov eax, DWORD PTR [edi+8228]
	cmp eax, 384
	je 212f
	mov eax, 0
	cmp eax, 1
	jmp 213f
212:
	mov eax, DWORD PTR [edi+8232]
	cmp eax, 32
213:
	je 214f
	mov eax, DWORD PTR [edi+8228]
	cmp eax, 256
	je 216f
	mov eax, 0
	cmp eax, 1
	jmp 217f
216:
	mov eax, DWORD PTR [edi+8232]
	cmp eax, 20
217:
	je 218f
	mov eax, 0
	jmp 219f
218:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
220:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 220b
	mov eax, 0
	mov ebp, edi
221:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 221b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
222:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 222b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
223:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 223b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
224:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 224b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
225:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 225b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
226:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 226b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+36], edx
	mov edx, 0
	mov DWORD PTR [edi+40], edx
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+56], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
227:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 227b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
228:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 228b
	mov eax, -2147483648
	mov DWORD PTR [edi+528], eax
	mov ecx, 0
	mov ebp, edi
229:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 229b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
230:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 230b
	mov eax, 1
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
231:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 231b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov edx, 0
	mov DWORD PTR [edi+48], edx
	mov edx, 0
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+64]
	and edx, DWORD PTR [edi+56]
	and edx, 1
	mov eax, 0
	sub eax, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+44]
	mov ebx, DWORD PTR [edi+48]
	or ebx, DWORD PTR [edi+44]
	or ebx, DWORD PTR [edi+52]
	and ebx, DWORD PTR [edi+36]
	or eax, ebx
	mov ebx, DWORD PTR [edi+40]
	and ebx, DWORD PTR [edi+52]
	or eax, ebx
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+44]
	and eax, 20
	mov edx, DWORD PTR [edi+48]
	and edx, 28
	or edx, eax
	mov eax, DWORD PTR [edi+52]
	and eax, 32
	or edx, eax
	mov eax, DWORD PTR [edi+8236]
	cmp eax, edx
	sbb ebx, ebx
	xor eax, edx
	and eax, ebx
	xor edx, eax
	mov DWORD PTR [edi+8240], edx
	mov eax, DWORD PTR [edi+8244]
	cmp eax, 0
	je 232f
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
234:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 234b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
235:
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 235b
	mov eax, 2
	mov DWORD PTR [edi+456], eax
	mov ecx, 0
	mov ebp, edi
236:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+456]
	mov DWORD PTR [ebp+400], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 236b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
237:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 237b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
238:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 238b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
239:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 239b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
240:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 240b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
241:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 241b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
242:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 242b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
243:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 243b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
244:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 244b
	mov eax, 0
	mov ebp, edi
245:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 245b
	mov eax, 593
	push eax
	push edi
	call {vg_dsa_pow_32_5}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
246:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 246b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
247:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 247b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14944
	mov ebx, 256
	mov eax, 71
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14720
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
248:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 248b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
249:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 249b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
250:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 250b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
251:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 251b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_pow_3_5}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14784
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
252:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 252b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
253:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 253b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
254:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 254b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
255:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 255b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_mulmod_3}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
256:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 256b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
257:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 257b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8220]
	mov ebx, DWORD PTR [edi+8240]
	mov eax, 71
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14880
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
258:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 258b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
259:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 259b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
260:
	mov DWORD PTR [ebp+232], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 260b
	mov eax, 1
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov ebp, edi
261:
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 261b
	mov eax, 1
	mov DWORD PTR [edi+288], eax
	mov esi, 384
262:
	mov ecx, 0
	mov ebp, edi
263:
	mov eax, DWORD PTR [ebp+288]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 263b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
264:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 264b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
265:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 265b
	sub esi, 1
	cmp esi, 0
	jne 262b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
266:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 266b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
267:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 267b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
268:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+512]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 268b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
269:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 269b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
270:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 270b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
271:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 271b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
272:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 272b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
273:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 273b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
274:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 274b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_mulmod_3}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14752
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
275:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 275b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
276:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 276b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
277:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 277b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
278:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 278b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
279:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 279b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
280:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 280b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
281:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 281b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
282:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 282b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 20
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
283:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 283b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 233f
232:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
284:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 284b
233:
219:
	jmp 215f
214:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
285:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 285b
	mov eax, 0
	mov ebp, edi
286:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 286b
	mov eax, -2147483648
	mov DWORD PTR [edi+6396], eax
	mov ecx, 0
	mov ebp, edi
287:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 287b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
288:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 288b
	mov eax, 1
	mov DWORD PTR [edi+6400], eax
	mov ecx, 0
	mov ebp, edi
289:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 289b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
290:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 290b
	mov eax, -2147483648
	mov DWORD PTR [edi+6524], eax
	mov ecx, 0
	mov ebp, edi
291:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 291b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
292:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 292b
	mov eax, 1
	mov DWORD PTR [edi+6528], eax
	mov ecx, 0
	mov ebp, edi
293:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 293b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+36], edx
	mov eax, 0
	mov ebp, edi
294:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 294b
	mov eax, -2147483648
	mov DWORD PTR [edi+6652], eax
	mov ecx, 0
	mov ebp, edi
295:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 295b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+40], edx
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+56], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
296:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 296b
	mov eax, 0
	mov ebp, edi
297:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 297b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
298:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 298b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
299:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 299b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2100:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2100b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2101:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2101b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2102:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2102b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2103:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2103b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2104:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2104b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2105:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2105b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2106:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2106b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+64]
	and edx, DWORD PTR [edi+56]
	and edx, 1
	mov eax, 0
	sub eax, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+44]
	mov ebx, DWORD PTR [edi+48]
	or ebx, DWORD PTR [edi+44]
	or ebx, DWORD PTR [edi+52]
	and ebx, DWORD PTR [edi+36]
	or eax, ebx
	mov ebx, DWORD PTR [edi+40]
	and ebx, DWORD PTR [edi+52]
	or eax, ebx
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+44]
	and eax, 20
	mov edx, DWORD PTR [edi+48]
	and edx, 28
	or edx, eax
	mov eax, DWORD PTR [edi+52]
	and eax, 32
	or edx, eax
	mov eax, DWORD PTR [edi+8236]
	cmp eax, edx
	sbb ebx, ebx
	xor eax, edx
	and eax, ebx
	xor edx, eax
	mov DWORD PTR [edi+8240], edx
	mov eax, DWORD PTR [edi+8244]
	cmp eax, 0
	je 2107f
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2109:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2109b
	mov eax, 0
	mov ebp, edi
2110:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2110b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2111:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+568]
	mov DWORD PTR [ebp+496], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2111b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2112:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2112b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2113:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2113b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2114:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2114b
	mov ecx, 0
	mov ebp, edi
2115:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2115b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2116:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2116b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2117:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2117b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2118:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2118b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2119:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2119b
	mov eax, 0
	mov ebp, edi
2120:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 2120b
	mov eax, 881
	push eax
	push edi
	call {vg_dsa_pow_48_8}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2121:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2121b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2122:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2122b
	mov esi, edi
	add esi, 14944
	mov ebx, 384
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14720
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2123:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2123b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2124:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2124b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2125:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2125b
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2126:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2126b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_pow_4_8}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14784
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2127:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2127b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2128:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2128b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2129:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2129b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2130:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2130b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2131:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2131b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2132:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2132b
	mov esi, DWORD PTR [edi+8220]
	mov ebx, DWORD PTR [edi+8240]
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14880
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2133:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2133b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2134:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2134b
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
2135:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2135b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2136:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2136b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2137:
	mov ecx, 0
	mov ebp, edi
2138:
	mov eax, DWORD PTR [ebp+352]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+352]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2138b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2139:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2139b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2140:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2140b
	sub esi, 1
	cmp esi, 0
	jne 2137b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2141:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2141b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2142:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2142b
	mov ecx, 0
	mov ebp, edi
2143:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+640]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2143b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2144:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2144b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2145:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+496], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2145b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2146:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2146b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2147:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2147b
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2148:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2148b
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2149:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2149b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14752
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2150:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2150b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2151:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2151b
	mov ecx, 0
	mov ebp, edi
2152:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2152b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2153:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2153b
	mov ecx, 0
	mov ebp, edi
2154:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2154b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2155:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2155b
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2156:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2156b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2157:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2157b
	mov esi, DWORD PTR [edi+8224]
	add esi, 32
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2158:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2158b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2108f
2107:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2159:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2159b
2108:
215:
	jmp 211f
210:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2160:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2160b
	mov eax, 0
	mov ebp, edi
2161:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2161b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2162:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2162b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2163:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2163b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2164:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2164b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2165:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2165b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2166:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2166b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+36], edx
	mov edx, 0
	mov DWORD PTR [edi+40], edx
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+56], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2167:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2167b
	mov eax, 0
	mov ebp, edi
2168:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2168b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2169:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2169b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2170:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2170b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2171:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2171b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2172:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2172b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2173:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2173b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2174:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2174b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2175:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2175b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2176:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2176b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2177:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2177b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+64]
	and edx, DWORD PTR [edi+56]
	and edx, 1
	mov eax, 0
	sub eax, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+44]
	mov ebx, DWORD PTR [edi+48]
	or ebx, DWORD PTR [edi+44]
	or ebx, DWORD PTR [edi+52]
	and ebx, DWORD PTR [edi+36]
	or eax, ebx
	mov ebx, DWORD PTR [edi+40]
	and ebx, DWORD PTR [edi+52]
	or eax, ebx
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+44]
	and eax, 20
	mov edx, DWORD PTR [edi+48]
	and edx, 28
	or edx, eax
	mov eax, DWORD PTR [edi+52]
	and eax, 32
	or edx, eax
	mov eax, DWORD PTR [edi+8236]
	cmp eax, edx
	sbb ebx, ebx
	xor eax, edx
	and eax, ebx
	xor edx, eax
	mov DWORD PTR [edi+8240], edx
	mov eax, DWORD PTR [edi+8244]
	cmp eax, 0
	je 2178f
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2180:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2180b
	mov eax, 0
	mov ebp, edi
2181:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2181b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2182:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+568]
	mov DWORD PTR [ebp+496], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2182b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2183:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2183b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2184:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2184b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2185:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2185b
	mov ecx, 0
	mov ebp, edi
2186:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2186b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2187:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2187b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2188:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2188b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2189:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2189b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2190:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2190b
	mov eax, 0
	mov ebp, edi
2191:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2191b
	mov eax, 593
	push eax
	push edi
	call {vg_dsa_pow_32_8}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2192:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2192b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2193:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2193b
	mov esi, edi
	add esi, 14944
	mov ebx, 256
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14720
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2194:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2194b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2195:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2195b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2196:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2196b
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2197:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2197b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_pow_4_8}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14784
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2198:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2198b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2199:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2199b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2200:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2200b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2201:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2201b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2202:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2202b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2203:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2203b
	mov esi, DWORD PTR [edi+8220]
	mov ebx, DWORD PTR [edi+8240]
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14880
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2204:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2204b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2205:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2205b
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
2206:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2206b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2207:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2207b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2208:
	mov ecx, 0
	mov ebp, edi
2209:
	mov eax, DWORD PTR [ebp+352]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+352]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2209b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2210:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2210b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2211:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2211b
	sub esi, 1
	cmp esi, 0
	jne 2208b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2212:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2212b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2213:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2213b
	mov ecx, 0
	mov ebp, edi
2214:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+640]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2214b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2215:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2215b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2216:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+496], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2216b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2217:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2217b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2218:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2218b
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2219:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2219b
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2220:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2220b
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14752
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2221:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2221b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2222:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2222b
	mov ecx, 0
	mov ebp, edi
2223:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2223b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2224:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2224b
	mov ecx, 0
	mov ebp, edi
2225:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2225b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2226:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2226b
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2227:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2227b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2228:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2228b
	mov esi, DWORD PTR [edi+8224]
	add esi, 32
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2229:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2229b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2179f
2178:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2230:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2230b
2179:
211:
	jmp 27f
26:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2231:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2231b
	mov eax, 0
	mov ebp, edi
2232:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2232b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2233:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2233b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2234:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2234b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2235:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2235b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2236:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2236b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2237:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2237b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+36], edx
	mov edx, 0
	mov DWORD PTR [edi+40], edx
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+56], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2238:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2238b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 0
	mov ebp, edi
2239:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2239b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2240:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2240b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2241:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2241b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2242:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2242b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2243:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2243b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2244:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2244b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2245:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2245b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2246:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2246b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2247:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2247b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2248:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2248b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+64]
	and edx, DWORD PTR [edi+56]
	and edx, 1
	mov eax, 0
	sub eax, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+44]
	mov ebx, DWORD PTR [edi+48]
	or ebx, DWORD PTR [edi+44]
	or ebx, DWORD PTR [edi+52]
	and ebx, DWORD PTR [edi+36]
	or eax, ebx
	mov ebx, DWORD PTR [edi+40]
	and ebx, DWORD PTR [edi+52]
	or eax, ebx
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+44]
	and eax, 20
	mov edx, DWORD PTR [edi+48]
	and edx, 28
	or edx, eax
	mov eax, DWORD PTR [edi+52]
	and eax, 32
	or edx, eax
	mov eax, DWORD PTR [edi+8236]
	cmp eax, edx
	sbb ebx, ebx
	xor eax, edx
	and eax, ebx
	xor edx, eax
	mov DWORD PTR [edi+8240], edx
	mov eax, DWORD PTR [edi+8244]
	cmp eax, 0
	je 2249f
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2251:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2251b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 0
	mov ebp, edi
2252:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2252b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2253:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+568]
	mov DWORD PTR [ebp+496], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2253b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2254:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2254b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2255:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2255b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2256:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2256b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2257:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2257b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2258:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2258b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2259:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2259b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2260:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2260b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2261:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2261b
	mov eax, 0
	mov ebp, edi
2262:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2262b
	mov eax, 593
	push eax
	push edi
	call {vg_dsa_pow_32_7}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2263:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2263b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2264:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2264b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, edi
	add esi, 14944
	mov ebx, 256
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14720
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2265:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2265b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2266:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2266b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2267:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2267b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2268:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2268b
	mov eax, 0
	mov DWORD PTR [edi+668], eax
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_pow_4_7}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14784
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2269:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2269b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2270:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2270b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2271:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2271b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2272:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2272b
	mov eax, 0
	mov DWORD PTR [edi+668], eax
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2273:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2273b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2274:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2274b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8220]
	mov ebx, DWORD PTR [edi+8240]
	mov eax, 89
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_4}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14880
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2275:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2275b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2276:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2276b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
2277:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2277b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2278:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2278b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2279:
	mov ecx, 0
	mov ebp, edi
2280:
	mov eax, DWORD PTR [ebp+352]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+352]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2280b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2281:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2281b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2282:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2282b
	sub esi, 1
	cmp esi, 0
	jne 2279b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2283:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2283b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2284:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2284b
	mov eax, 0
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2285:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+640]
	mov DWORD PTR [ebp+208], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2285b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2286:
	mov eax, DWORD PTR [ebp+208]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+136], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2286b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2287:
	mov eax, DWORD PTR [ebp+208]
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+496], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2287b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2288:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2288b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2289:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2289b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2290:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2290b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2291:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2291b
	mov eax, 0
	mov DWORD PTR [edi+668], eax
	mov eax, 89
	push eax
	push edi
	call {vg_dsa_mulmod_4}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14752
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2292:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2292b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2293:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2293b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2294:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2294b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2295:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2295b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2296:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2296b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2297:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2297b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2298:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2298b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2299:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2299b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 28
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2300:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2300b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2250f
2249:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2301:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2301b
2250:
27:
	jmp 23f
22:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2302:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2302b
	mov eax, 0
	mov ebp, edi
2303:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2303b
	mov eax, -2147483648
	mov DWORD PTR [edi+2300], eax
	mov ecx, 0
	mov ebp, edi
2304:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2304b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov edx, ebx
	mov DWORD PTR [edi+32], edx
	mov edx, 0
	mov DWORD PTR [edi+36], edx
	mov edx, 0
	mov DWORD PTR [edi+40], edx
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+56], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2305:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2305b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
2306:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2306b
	mov eax, -2147483648
	mov DWORD PTR [edi+528], eax
	mov ecx, 0
	mov ebp, edi
2307:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2307b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2308:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2308b
	mov eax, 1
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2309:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2309b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov edx, 0
	mov DWORD PTR [edi+48], edx
	mov edx, 0
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+64]
	and edx, DWORD PTR [edi+56]
	and edx, 1
	mov eax, 0
	sub eax, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+44]
	mov ebx, DWORD PTR [edi+48]
	or ebx, DWORD PTR [edi+44]
	or ebx, DWORD PTR [edi+52]
	and ebx, DWORD PTR [edi+36]
	or eax, ebx
	mov ebx, DWORD PTR [edi+40]
	and ebx, DWORD PTR [edi+52]
	or eax, ebx
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+44]
	and eax, 20
	mov edx, DWORD PTR [edi+48]
	and edx, 28
	or edx, eax
	mov eax, DWORD PTR [edi+52]
	and eax, 32
	or edx, eax
	mov eax, DWORD PTR [edi+8236]
	cmp eax, edx
	sbb ebx, ebx
	xor eax, edx
	and eax, ebx
	xor edx, eax
	mov DWORD PTR [edi+8240], edx
	mov eax, DWORD PTR [edi+8244]
	cmp eax, 0
	je 2310f
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2312:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2312b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
2313:
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2313b
	mov eax, 2
	mov DWORD PTR [edi+456], eax
	mov ecx, 0
	mov ebp, edi
2314:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+456]
	mov DWORD PTR [ebp+400], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2314b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2315:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2315b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2316:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2316b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2317:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2317b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2318:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2318b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2319:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2319b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2320:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2320b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2321:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2321b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2322:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2322b
	mov eax, 0
	mov ebp, edi
2323:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2323b
	mov eax, 305
	push eax
	push edi
	call {vg_dsa_pow_16_5}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2324:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2324b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2325:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2325b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14944
	mov ebx, 128
	mov eax, 71
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14720
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2326:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2326b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2327:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2327b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2328:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2328b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2329:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2329b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_pow_3_5}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14784
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2330:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2330b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2331:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2331b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2332:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2332b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2333:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2333b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_mulmod_3}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2334:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2334b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2335:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2335b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8220]
	mov ebx, DWORD PTR [edi+8240]
	mov eax, 71
	push ebx
	push esi
	push eax
	push edi
	call {vg_dsa_reduce_3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, edi
	add esi, 14880
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2336:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2336b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2337:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2337b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov ebx, DWORD PTR [edi+64]
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
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
2338:
	mov DWORD PTR [ebp+232], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2338b
	mov eax, 1
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov ebp, edi
2339:
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2339b
	mov eax, 1
	mov DWORD PTR [edi+288], eax
	mov esi, 384
2340:
	mov ecx, 0
	mov ebp, edi
2341:
	mov eax, DWORD PTR [ebp+288]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2341b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2342:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2342b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2343:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2343b
	sub esi, 1
	cmp esi, 0
	jne 2340b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2344:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2344b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2345:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2345b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2346:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+512]
	mov DWORD PTR [ebp+176], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2346b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2347:
	mov eax, DWORD PTR [ebp+176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+120], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2347b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2348:
	mov eax, DWORD PTR [ebp+176]
	mov edx, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+400], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2348b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2349:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2349b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2350:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2350b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2351:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2351b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2352:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2352b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, 71
	push eax
	push edi
	call {vg_dsa_mulmod_3}
	pop eax
	pop eax
	mov esi, edi
	add esi, 14752
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2353:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2353b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2354:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2354b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2355:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2355b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2356:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2356b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2357:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2357b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2358:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2358b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2359:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2359b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2360:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2360b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 20
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2361:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2361b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2311f
2310:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2362:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2362b
2311:
23:
	mov ebx, DWORD PTR [edi+8256]
	mov ebp, DWORD PTR [edi+8260]
	mov esi, DWORD PTR [edi+8264]
	mov edi, DWORD PTR [edi+8268]
	ret
	.p2align 6
