// The functions of `src/internal/vg_dsa_sign.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign:
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
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
220:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 220b
	jmp 219f
218:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
221:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 221b
	mov eax, 0
	mov ebp, edi
222:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 222b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
223:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 223b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
224:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 224b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
225:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 225b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
226:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 226b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
227:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 227b
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
228:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 228b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
229:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 229b
	mov eax, -2147483648
	mov DWORD PTR [edi+528], eax
	mov ecx, 0
	mov ebp, edi
230:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 230b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
231:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 231b
	mov eax, 1
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
232:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 232b
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
	je 233f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
235:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 235b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
236:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 236b
	mov ecx, 0
	mov ebp, edi
237:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 237b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
238:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 238b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
239:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 239b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
240:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 240b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
241:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 241b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
242:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 242b
	mov ecx, 0
	mov ebp, edi
243:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 243b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
244:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 244b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
245:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 245b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
246:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 246b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
247:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 247b
	mov eax, 0
	mov ebp, edi
248:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 248b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
249:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	mov DWORD PTR [ebp+3184], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 249b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
250:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 250b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
251:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 251b
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
	add esi, 14816
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
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
253:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 253b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
254:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 254b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
255:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 255b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
256:
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 256b
	mov eax, 2
	mov DWORD PTR [edi+456], eax
	mov ecx, 0
	mov ebp, edi
257:
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
	jne 257b
	mov esi, edi
	add esi, 14912
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
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
259:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 259b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
260:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 260b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
261:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 261b
	mov eax, 0
	mov ebp, edi
262:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 262b
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
263:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 263b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
264:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 264b
	mov eax, 0
	mov ebp, edi
265:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 265b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
266:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 266b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
267:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 267b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
268:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 268b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
269:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 269b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
270:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 270b
	mov eax, 0
	mov ebp, edi
271:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 271b
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
272:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 272b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
273:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 273b
	mov eax, 0
	mov ebp, edi
274:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 274b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
275:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 275b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
276:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 276b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
277:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 277b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
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
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 279b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
280:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 280b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
281:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 281b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
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
	mov ecx, 0
	mov ebp, edi
283:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 283b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
284:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 284b
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
285:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 285b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
286:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 286b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
287:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 287b
	mov eax, 0
	mov ebp, edi
288:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 288b
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
289:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 289b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
290:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 290b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
291:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 291b
	mov ecx, 0
	mov ebp, edi
292:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 292b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
293:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 293b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
294:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 294b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
295:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 295b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
296:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 296b
	mov eax, 0
	mov ebp, edi
297:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 297b
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
298:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 298b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
299:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 299b
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
2100:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2100b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2101:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2101b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2102:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2102b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2103:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2103b
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
2104:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2104b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2105:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2105b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2106:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2106b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2107:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2107b
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
2108:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2108b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2109:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2109b
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
2110:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2110b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2111:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2111b
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
2112:
	mov DWORD PTR [ebp+232], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2112b
	mov eax, 1
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov ebp, edi
2113:
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2113b
	mov eax, 1
	mov DWORD PTR [edi+288], eax
	mov esi, 384
2114:
	mov ecx, 0
	mov ebp, edi
2115:
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
	jne 2115b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2116:
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
	jne 2116b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2117:
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
	jne 2117b
	sub esi, 1
	cmp esi, 0
	jne 2114b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2118:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2118b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2119:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2119b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2120:
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
	jne 2120b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2121:
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
	jne 2121b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2122:
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
	jne 2122b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2123:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2123b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2124:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2124b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2125:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2125b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2126:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2126b
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
2127:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2127b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2128:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2128b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2129:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2129b
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
2130:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2130b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2131:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2131b
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
2132:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2132b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2133:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2133b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2134:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2134b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 20
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2135:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2135b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 234f
233:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2136:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2136b
234:
219:
	jmp 215f
214:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2137:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2137b
	mov eax, 0
	mov ebp, edi
2138:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2138b
	mov eax, -2147483648
	mov DWORD PTR [edi+6396], eax
	mov ecx, 0
	mov ebp, edi
2139:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2139b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2140:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2140b
	mov eax, 1
	mov DWORD PTR [edi+6400], eax
	mov ecx, 0
	mov ebp, edi
2141:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2141b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2142:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2142b
	mov eax, -2147483648
	mov DWORD PTR [edi+6524], eax
	mov ecx, 0
	mov ebp, edi
2143:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2143b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2144:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2144b
	mov eax, 1
	mov DWORD PTR [edi+6528], eax
	mov ecx, 0
	mov ebp, edi
2145:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2145b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+36], edx
	mov eax, 0
	mov ebp, edi
2146:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2146b
	mov eax, -2147483648
	mov DWORD PTR [edi+6652], eax
	mov ecx, 0
	mov ebp, edi
2147:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2147b
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
2148:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2148b
	mov eax, 0
	mov ebp, edi
2149:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2149b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2150:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2150b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2151:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2151b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2152:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2152b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2153:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2153b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2154:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2154b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2155:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2155b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2156:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2156b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2157:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2157b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2158:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2158b
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
	je 2159f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2161:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2161b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2162:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2162b
	mov ecx, 0
	mov ebp, edi
2163:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2163b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2164:
	or ecx, DWORD PTR [ebp+3944]
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2164b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2165:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2165b
	mov eax, 2
	mov DWORD PTR [edi+5496], eax
	mov ecx, 0
	mov ebp, edi
2166:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+5496]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2166b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2167:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2167b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2168:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2168b
	mov ecx, 0
	mov ebp, edi
2169:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2169b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2170:
	or ecx, DWORD PTR [ebp+3944]
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2170b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2171:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2171b
	mov eax, 2
	mov DWORD PTR [edi+5496], eax
	mov ecx, 0
	mov ebp, edi
2172:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+5496]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2172b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2173:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2173b
	mov eax, 0
	mov ebp, edi
2174:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2174b
	mov eax, 1
	mov DWORD PTR [edi+5496], eax
	mov ecx, 0
	mov ebp, edi
2175:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+5496]
	mov DWORD PTR [ebp+4720], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2175b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2176:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2176b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2177:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2177b
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
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2178:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2178b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2179:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2179b
	mov ecx, 0
	mov ebp, edi
2180:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2180b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2181:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2181b
	mov eax, 0
	mov ebp, edi
2182:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2182b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2183:
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
	jne 2183b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2184:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2184b
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2185:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2185b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2186:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2186b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2187:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2187b
	mov eax, 0
	mov ebp, edi
2188:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 2188b
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
2189:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2189b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2190:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2190b
	mov eax, 0
	mov ebp, edi
2191:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2191b
	mov eax, 1
	mov DWORD PTR [edi+6272], eax
	mov ecx, 0
	mov ebp, edi
2192:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2192b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2193:
	mov eax, DWORD PTR [ebp+6272]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3944]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2193b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2194:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2194b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2195:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2195b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2196:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2196b
	mov eax, 0
	mov ebp, edi
2197:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 2197b
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
2198:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2198b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2199:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2199b
	mov eax, 0
	mov ebp, edi
2200:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2200b
	mov eax, 1
	mov DWORD PTR [edi+6272], eax
	mov ecx, 0
	mov ebp, edi
2201:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2201b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2202:
	mov eax, DWORD PTR [ebp+6272]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3944]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2202b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
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
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2204:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2204b
	mov ecx, 0
	mov ebp, edi
2205:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2205b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2206:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2206b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2207:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2207b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2208:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2208b
	mov ecx, 0
	mov ebp, edi
2209:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2209b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2210:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2210b
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
2211:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2211b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2212:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2212b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2213:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2213b
	mov eax, 0
	mov ebp, edi
2214:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 2214b
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
2215:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2215b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2216:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2216b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2217:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2217b
	mov ecx, 0
	mov ebp, edi
2218:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2218b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2219:
	mov eax, DWORD PTR [ebp+6272]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3944]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2219b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2220:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2220b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2221:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2221b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2222:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2222b
	mov eax, 0
	mov ebp, edi
2223:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 2223b
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
2224:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2224b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2225:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2225b
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
2226:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2226b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2227:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2227b
	mov esi, DWORD PTR [edi+8216]
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
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2229:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2229b
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
2230:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2230b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2231:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2231b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2232:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2232b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2233:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2233b
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
2234:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2234b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2235:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2235b
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
2236:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2236b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2237:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2237b
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
2238:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2238b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2239:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2239b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2240:
	mov ecx, 0
	mov ebp, edi
2241:
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
	jne 2241b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2242:
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
	jne 2242b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2243:
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
	jne 2243b
	sub esi, 1
	cmp esi, 0
	jne 2240b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2244:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2244b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2245:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2245b
	mov ecx, 0
	mov ebp, edi
2246:
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
	jne 2246b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2247:
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
	jne 2247b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2248:
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
	jne 2248b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2249:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2249b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2250:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2250b
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2251:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2251b
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2252:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2252b
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
2253:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2253b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2254:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2254b
	mov ecx, 0
	mov ebp, edi
2255:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2255b
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
2256:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2256b
	mov ecx, 0
	mov ebp, edi
2257:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2257b
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
2258:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2258b
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2259:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2259b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2260:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2260b
	mov esi, DWORD PTR [edi+8224]
	add esi, 32
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2261:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2261b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2160f
2159:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2262:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2262b
2160:
215:
	jmp 211f
210:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2263:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2263b
	mov eax, 0
	mov ebp, edi
2264:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2264b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2265:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2265b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2266:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2266b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2267:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2267b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2268:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2268b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2269:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2269b
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
2270:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2270b
	mov eax, 0
	mov ebp, edi
2271:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2271b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2272:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2272b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2273:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2273b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2274:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2274b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2275:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2275b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2276:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2276b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2277:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2277b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2278:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2278b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2279:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2279b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2280:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2280b
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
	je 2281f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2283:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2283b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2284:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2284b
	mov ecx, 0
	mov ebp, edi
2285:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2285b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2286:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2286b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2287:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2287b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2288:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2288b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2289:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2289b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2290:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2290b
	mov ecx, 0
	mov ebp, edi
2291:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2291b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2292:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2292b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2293:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2293b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2294:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2294b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2295:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2295b
	mov eax, 0
	mov ebp, edi
2296:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2296b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2297:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	mov DWORD PTR [ebp+3184], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2297b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2298:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2298b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2299:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2299b
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
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2300:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2300b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2301:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2301b
	mov ecx, 0
	mov ebp, edi
2302:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2302b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2303:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2303b
	mov eax, 0
	mov ebp, edi
2304:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2304b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2305:
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
	jne 2305b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2306:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2306b
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2307:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2307b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2308:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2308b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2309:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2309b
	mov eax, 0
	mov ebp, edi
2310:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2310b
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
2311:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2311b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2312:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2312b
	mov eax, 0
	mov ebp, edi
2313:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2313b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2314:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2314b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2315:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2315b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2316:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2316b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2317:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2317b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2318:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2318b
	mov eax, 0
	mov ebp, edi
2319:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2319b
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
2320:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2320b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2321:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2321b
	mov eax, 0
	mov ebp, edi
2322:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2322b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2323:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2323b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2324:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2324b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2325:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2325b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2326:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2326b
	mov ecx, 0
	mov ebp, edi
2327:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2327b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2328:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2328b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2329:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2329b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2330:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2330b
	mov ecx, 0
	mov ebp, edi
2331:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2331b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2332:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2332b
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
2333:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2333b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2334:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2334b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2335:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2335b
	mov eax, 0
	mov ebp, edi
2336:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2336b
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
2337:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2337b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2338:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2338b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2339:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2339b
	mov ecx, 0
	mov ebp, edi
2340:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2340b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2341:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2341b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2342:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2342b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2343:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2343b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2344:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2344b
	mov eax, 0
	mov ebp, edi
2345:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2345b
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
2346:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2346b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2347:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2347b
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
2348:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2348b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2349:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2349b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2350:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2350b
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2351:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2351b
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
2352:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2352b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2353:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2353b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2354:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2354b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2355:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2355b
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
2356:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2356b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2357:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2357b
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
2358:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2358b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2359:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2359b
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
2360:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2360b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2361:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2361b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2362:
	mov ecx, 0
	mov ebp, edi
2363:
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
	jne 2363b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2364:
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
	jne 2364b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2365:
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
	jne 2365b
	sub esi, 1
	cmp esi, 0
	jne 2362b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2366:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2366b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2367:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2367b
	mov ecx, 0
	mov ebp, edi
2368:
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
	jne 2368b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2369:
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
	jne 2369b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2370:
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
	jne 2370b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2371:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2371b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2372:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2372b
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2373:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2373b
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2374:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2374b
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
2375:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2375b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2376:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2376b
	mov ecx, 0
	mov ebp, edi
2377:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2377b
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
2378:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2378b
	mov ecx, 0
	mov ebp, edi
2379:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2379b
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
2380:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2380b
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2381:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2381b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2382:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2382b
	mov esi, DWORD PTR [edi+8224]
	add esi, 32
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2383:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2383b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2282f
2281:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2384:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2384b
2282:
211:
	jmp 27f
26:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2385:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2385b
	mov eax, 0
	mov ebp, edi
2386:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2386b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2387:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2387b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2388:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2388b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2389:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2389b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2390:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2390b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2391:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2391b
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
2392:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2392b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 0
	mov ebp, edi
2393:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2393b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2394:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2394b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2395:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2395b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2396:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2396b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2397:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2397b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2398:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2398b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2399:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2399b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2400:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2400b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2401:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2401b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2402:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2402b
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
	je 2403f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2405:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2405b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2406:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2406b
	mov ecx, 0
	mov ebp, edi
2407:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2407b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2408:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2408b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2409:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2409b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2410:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2410b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2411:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2411b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2412:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2412b
	mov ecx, 0
	mov ebp, edi
2413:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2413b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2414:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2414b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2415:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2415b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2416:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2416b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2417:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2417b
	mov eax, 0
	mov ebp, edi
2418:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2418b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2419:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	mov DWORD PTR [ebp+3184], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2419b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2420:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2420b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2421:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2421b
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
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2422:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2422b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2423:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2423b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2424:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2424b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2425:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2425b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 0
	mov ebp, edi
2426:
	mov DWORD PTR [ebp+568], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2426b
	mov eax, 2
	mov DWORD PTR [edi+568], eax
	mov ecx, 0
	mov ebp, edi
2427:
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
	jne 2427b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2428:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2428b
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2429:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2429b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2430:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2430b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2431:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2431b
	mov eax, 0
	mov ebp, edi
2432:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2432b
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
2433:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2433b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2434:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2434b
	mov eax, 0
	mov ebp, edi
2435:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2435b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2436:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2436b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2437:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2437b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2438:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2438b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2439:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2439b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2440:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2440b
	mov eax, 0
	mov ebp, edi
2441:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2441b
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
2442:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2442b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2443:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2443b
	mov eax, 0
	mov ebp, edi
2444:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2444b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2445:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2445b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2446:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2446b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2447:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2447b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2448:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2448b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2449:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2449b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2450:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2450b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2451:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2451b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2452:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2452b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2453:
	mov eax, DWORD PTR [ebp+424]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2453b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2454:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2454b
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
2455:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2455b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2456:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2456b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2457:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2457b
	mov eax, 0
	mov ebp, edi
2458:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2458b
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
2459:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2459b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2460:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2460b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2461:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2461b
	mov ecx, 0
	mov ebp, edi
2462:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2462b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2463:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2463b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2464:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2464b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2465:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2465b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2466:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2466b
	mov eax, 0
	mov ebp, edi
2467:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2467b
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
2468:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2468b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2469:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2469b
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
2470:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2470b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2471:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2471b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2472:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2472b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2473:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2473b
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
2474:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2474b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2475:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2475b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2476:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2476b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2477:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2477b
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
2478:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2478b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2479:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2479b
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
2480:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2480b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2481:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2481b
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
2482:
	mov DWORD PTR [ebp+280], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2482b
	mov eax, 1
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov ebp, edi
2483:
	mov DWORD PTR [ebp+352], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2483b
	mov eax, 1
	mov DWORD PTR [edi+352], eax
	mov esi, 512
2484:
	mov ecx, 0
	mov ebp, edi
2485:
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
	jne 2485b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2486:
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
	jne 2486b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2487:
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
	jne 2487b
	sub esi, 1
	cmp esi, 0
	jne 2484b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2488:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2488b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2489:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2489b
	mov eax, 0
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2490:
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
	jne 2490b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+240], eax
	mov ecx, 0
	mov ebp, edi
2491:
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
	jne 2491b
	mov eax, DWORD PTR [edi+240]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2492:
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
	jne 2492b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2493:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2493b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2494:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2494b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2495:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2495b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2496:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+640], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2496b
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
2497:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2497b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2498:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2498b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2499:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2499b
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
2500:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2500b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov ecx, 0
	mov ebp, edi
2501:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2501b
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
2502:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2502b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2503:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2503b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2504:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2504b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 28
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2505:
	mov eax, DWORD PTR [ebp+424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2505b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2404f
2403:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2506:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2506b
2404:
27:
	jmp 23f
22:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2507:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2507b
	mov eax, 0
	mov ebp, edi
2508:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2508b
	mov eax, -2147483648
	mov DWORD PTR [edi+2300], eax
	mov ecx, 0
	mov ebp, edi
2509:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2509b
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
2510:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2510b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
2511:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2511b
	mov eax, -2147483648
	mov DWORD PTR [edi+528], eax
	mov ecx, 0
	mov ebp, edi
2512:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2512b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2513:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2513b
	mov eax, 1
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2514:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2514b
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
	je 2515f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2517:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2517b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2518:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2518b
	mov ecx, 0
	mov ebp, edi
2519:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2519b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2520:
	or ecx, DWORD PTR [ebp+1384]
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2520b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2521:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2521b
	mov eax, 2
	mov DWORD PTR [edi+1912], eax
	mov ecx, 0
	mov ebp, edi
2522:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1912]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2522b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2523:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2523b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2524:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2524b
	mov ecx, 0
	mov ebp, edi
2525:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2525b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2526:
	or ecx, DWORD PTR [ebp+1384]
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2526b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, 0
	mov ebp, edi
2527:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2527b
	mov eax, 2
	mov DWORD PTR [edi+1912], eax
	mov ecx, 0
	mov ebp, edi
2528:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1912]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2528b
	mov eax, ecx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2529:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2529b
	mov eax, 0
	mov ebp, edi
2530:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2530b
	mov eax, 1
	mov DWORD PTR [edi+1912], eax
	mov ecx, 0
	mov ebp, edi
2531:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1912]
	mov DWORD PTR [ebp+1648], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2531b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2532:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2532b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2533:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2533b
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
	add esi, 14816
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2534:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2534b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2535:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2535b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2536:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2536b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2537:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2537b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
2538:
	mov DWORD PTR [ebp+456], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2538b
	mov eax, 2
	mov DWORD PTR [edi+456], eax
	mov ecx, 0
	mov ebp, edi
2539:
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
	jne 2539b
	mov esi, edi
	add esi, 14912
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2540:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2540b
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2541:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2541b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2542:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2542b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2543:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2543b
	mov eax, 0
	mov ebp, edi
2544:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2544b
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
2545:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2545b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2546:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2546b
	mov eax, 0
	mov ebp, edi
2547:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2547b
	mov eax, 1
	mov DWORD PTR [edi+2176], eax
	mov ecx, 0
	mov ebp, edi
2548:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2548b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2549:
	mov eax, DWORD PTR [ebp+2176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1384]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2549b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2550:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2550b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2551:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2551b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2552:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2552b
	mov eax, 0
	mov ebp, edi
2553:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2553b
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
2554:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2554b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2555:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2555b
	mov eax, 0
	mov ebp, edi
2556:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2556b
	mov eax, 1
	mov DWORD PTR [edi+2176], eax
	mov ecx, 0
	mov ebp, edi
2557:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2557b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2558:
	mov eax, DWORD PTR [ebp+2176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1384]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2558b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2559:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2559b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2560:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2560b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2561:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2561b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2562:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2562b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2563:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2563b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2564:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2564b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2565:
	mov eax, DWORD PTR [ebp+344]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2565b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2566:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2566b
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
2567:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2567b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2568:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2568b
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2569:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2569b
	mov eax, 0
	mov ebp, edi
2570:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2570b
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
2571:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2571b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2572:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2572b
	mov esi, DWORD PTR [edi+8204]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2573:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2573b
	mov ecx, 0
	mov ebp, edi
2574:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2574b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2575:
	mov eax, DWORD PTR [ebp+2176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1384]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2575b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2576:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2576b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2577:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2577b
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2578:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2578b
	mov eax, 0
	mov ebp, edi
2579:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2579b
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
2580:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2580b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2581:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2581b
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
2582:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2582b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2583:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2583b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8216]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2584:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2584b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14912
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2585:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2585b
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
2586:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2586b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2587:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2587b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, DWORD PTR [edi+8208]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2588:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2588b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2589:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2589b
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
2590:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2590b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2591:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2591b
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
2592:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2592b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2593:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2593b
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
2594:
	mov DWORD PTR [ebp+232], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2594b
	mov eax, 1
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov ebp, edi
2595:
	mov DWORD PTR [ebp+288], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2595b
	mov eax, 1
	mov DWORD PTR [edi+288], eax
	mov esi, 384
2596:
	mov ecx, 0
	mov ebp, edi
2597:
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
	jne 2597b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2598:
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
	jne 2598b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2599:
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
	jne 2599b
	sub esi, 1
	cmp esi, 0
	jne 2596b
	mov esi, edi
	add esi, 14880
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2600:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2600b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2601:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2601b
	mov eax, 0
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2602:
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
	jne 2602b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+200], eax
	mov ecx, 0
	mov ebp, edi
2603:
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
	jne 2603b
	mov eax, DWORD PTR [edi+200]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
2604:
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
	jne 2604b
	mov esi, edi
	add esi, 14848
	mov ecx, -1
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2605:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2605b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2606:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2606b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov esi, edi
	add esi, 14784
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2607:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2607b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, edi
	add esi, 14848
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2608:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+512], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2608b
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
2609:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2609b
	mov esi, edi
	add esi, 14720
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2610:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2610b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2611:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2611b
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
2612:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2612b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2613:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2613b
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
2614:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2614b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2615:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2615b
	mov esi, edi
	add esi, 14752
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2616:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2616b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov esi, DWORD PTR [edi+8224]
	add esi, 20
	mov ecx, DWORD PTR [edi+8244]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2617:
	mov eax, DWORD PTR [ebp+344]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2617b
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2516f
2515:
	mov esi, DWORD PTR [edi+8224]
	mov ecx, DWORD PTR [edi+8232]
	add ecx, ecx
	mov eax, 0
2618:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 2618b
2516:
23:
	mov ebx, DWORD PTR [edi+8256]
	mov ebp, DWORD PTR [edi+8260]
	mov esi, DWORD PTR [edi+8264]
	mov edi, DWORD PTR [edi+8268]
	ret
	.p2align 6
