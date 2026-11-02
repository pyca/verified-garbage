// The functions of `src/internal/vg_dsa_check_parameters.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_check_parameters:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+8256], ebx
	mov DWORD PTR [eax+8260], ebp
	mov DWORD PTR [eax+8264], esi
	mov DWORD PTR [eax+8268], edi
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [edi+8192], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+8228], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+8232], eax
	mov eax, DWORD PTR [esp+12]
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
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
234:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 234b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
235:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 235b
	mov ecx, 0
	mov ebp, edi
236:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 236b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
237:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 237b
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
238:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 238b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
239:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 239b
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
240:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 240b
	mov eax, 0
	mov ebp, edi
241:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 241b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
242:
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
	jne 242b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
243:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 243b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
244:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 244b
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
245:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 245b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
246:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 246b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
247:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 247b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
248:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 248b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
249:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 249b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
250:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 250b
	mov eax, 0
	mov ebp, edi
251:
	mov DWORD PTR [ebp+4244], eax
	add ebp, 4
	mov edx, edi
	add edx, 236
	cmp ebp, edx
	jne 251b
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
252:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 252b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
253:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 253b
	mov eax, 0
	mov ebp, edi
254:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 254b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
255:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 255b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
256:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 256b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 233f
232:
	mov eax, 0
233:
219:
	jmp 215f
214:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
257:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 257b
	mov eax, 0
	mov ebp, edi
258:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 258b
	mov eax, -2147483648
	mov DWORD PTR [edi+6396], eax
	mov ecx, 0
	mov ebp, edi
259:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 259b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
260:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 260b
	mov eax, 1
	mov DWORD PTR [edi+6400], eax
	mov ecx, 0
	mov ebp, edi
261:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 261b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
262:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 262b
	mov eax, -2147483648
	mov DWORD PTR [edi+6524], eax
	mov ecx, 0
	mov ebp, edi
263:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 263b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
264:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 264b
	mov eax, 1
	mov DWORD PTR [edi+6528], eax
	mov ecx, 0
	mov ebp, edi
265:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 265b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+36], edx
	mov eax, 0
	mov ebp, edi
266:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 266b
	mov eax, -2147483648
	mov DWORD PTR [edi+6652], eax
	mov ecx, 0
	mov ebp, edi
267:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 267b
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
268:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 268b
	mov eax, 0
	mov ebp, edi
269:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 269b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
270:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 270b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
271:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 271b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
272:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 272b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
273:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 273b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
274:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 274b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
275:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 275b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
276:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 276b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
277:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 277b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
278:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 278b
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
	je 279f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
281:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 281b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
282:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 282b
	mov ecx, 0
	mov ebp, edi
283:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 283b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
284:
	or ecx, DWORD PTR [ebp+3944]
	add ebp, 4
	mov edx, edi
	add edx, 384
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
	mov eax, 0
	mov ebp, edi
285:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 285b
	mov eax, 2
	mov DWORD PTR [edi+5496], eax
	mov ecx, 0
	mov ebp, edi
286:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+5496]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 286b
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
287:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 287b
	mov eax, 0
	mov ebp, edi
288:
	mov DWORD PTR [ebp+5496], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 288b
	mov eax, 1
	mov DWORD PTR [edi+5496], eax
	mov ecx, 0
	mov ebp, edi
289:
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
	jne 289b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
290:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 290b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
291:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 291b
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
292:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 292b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
293:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 293b
	mov ecx, 0
	mov ebp, edi
294:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 294b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
295:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 295b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
296:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 296b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
297:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+6272], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 297b
	mov eax, 0
	mov ebp, edi
298:
	mov DWORD PTR [ebp+6304], eax
	add ebp, 4
	mov edx, edi
	add edx, 352
	cmp ebp, edx
	jne 298b
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
299:
	mov eax, DWORD PTR [ebp+4720]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 299b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 380
	mov ebp, edi
2100:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+3944], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2100b
	mov eax, 0
	mov ebp, edi
2101:
	mov DWORD PTR [ebp+6272], eax
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2101b
	mov eax, 1
	mov DWORD PTR [edi+6272], eax
	mov ecx, 0
	mov ebp, edi
2102:
	mov eax, DWORD PTR [ebp+3944]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+6272]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2102b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2103:
	mov eax, DWORD PTR [ebp+6272]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3944]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 384
	cmp ebp, edx
	jne 2103b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 280f
279:
	mov eax, 0
280:
215:
	jmp 211f
210:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2104:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2104b
	mov eax, 0
	mov ebp, edi
2105:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2105b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2106:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2106b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2107:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2107b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2108:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2108b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2109:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2109b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2110:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2110b
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
2111:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2111b
	mov eax, 0
	mov ebp, edi
2112:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2112b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
	mov ecx, 0
	mov ebp, edi
2113:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2113b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2114:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2114b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
	mov ecx, 0
	mov ebp, edi
2115:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2115b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2116:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2116b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2117:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2117b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2118:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2118b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2119:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2119b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2120:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2120b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2121:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2121b
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
	je 2122f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2124:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2124b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2125:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2125b
	mov ecx, 0
	mov ebp, edi
2126:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2126b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2127:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2127b
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
2128:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2128b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2129:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2129b
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
2130:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2130b
	mov eax, 0
	mov ebp, edi
2131:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2131b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2132:
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
	jne 2132b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2133:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
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
2135:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2135b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2136:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2136b
	mov ecx, 0
	mov ebp, edi
2137:
	or ecx, DWORD PTR [ebp+424]
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2137b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2138:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2138b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2139:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2139b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 28
	mov ebp, edi
2140:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2140b
	mov eax, 0
	mov ebp, edi
2141:
	mov DWORD PTR [ebp+4256], eax
	add ebp, 4
	mov edx, edi
	add edx, 224
	cmp ebp, edx
	jne 2141b
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
2142:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2142b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2143:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2143b
	mov eax, 0
	mov ebp, edi
2144:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2144b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2145:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2145b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2146:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2146b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2123f
2122:
	mov eax, 0
2123:
211:
	jmp 27f
26:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2147:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2147b
	mov eax, 0
	mov ebp, edi
2148:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2148b
	mov eax, -2147483648
	mov DWORD PTR [edi+4348], eax
	mov ecx, 0
	mov ebp, edi
2149:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2149b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2150:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2150b
	mov eax, 1
	mov DWORD PTR [edi+4352], eax
	mov ecx, 0
	mov ebp, edi
2151:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2151b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+32], edx
	mov eax, 0
	mov ebp, edi
2152:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2152b
	mov eax, -2147483648
	mov DWORD PTR [edi+4476], eax
	mov ecx, 0
	mov ebp, edi
2153:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2153b
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
2154:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2154b
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 0
	mov ebp, edi
2155:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2155b
	mov eax, -2147483648
	mov DWORD PTR [edi+656], eax
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
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2157:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2157b
	mov eax, 1
	mov DWORD PTR [edi+660], eax
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
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+44], edx
	mov eax, 0
	mov ebp, edi
2159:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2159b
	mov eax, -2147483648
	mov DWORD PTR [edi+664], eax
	mov ecx, 0
	mov ebp, edi
2160:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2160b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2161:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2161b
	mov eax, 1
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2162:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2162b
	mov eax, ecx
	and eax, ebx
	mov edx, eax
	mov DWORD PTR [edi+48], edx
	mov eax, 0
	mov ebp, edi
2163:
	mov DWORD PTR [ebp+640], eax
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2163b
	mov eax, -2147483648
	mov DWORD PTR [edi+668], eax
	mov ecx, 0
	mov ebp, edi
2164:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+640]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 32
	cmp ebp, edx
	jne 2164b
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
	je 2165f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2167:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2167b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2168:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2168b
	mov ecx, 0
	mov ebp, edi
2169:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2169b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2170:
	or ecx, DWORD PTR [ebp+2664]
	add ebp, 4
	mov edx, edi
	add edx, 256
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
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2171b
	mov eax, 2
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2172:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+3704]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
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
	add ebx, 252
	mov ebp, edi
2173:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2173b
	mov eax, 0
	mov ebp, edi
2174:
	mov DWORD PTR [ebp+3704], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2174b
	mov eax, 1
	mov DWORD PTR [edi+3704], eax
	mov ecx, 0
	mov ebp, edi
2175:
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
	jne 2175b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2176:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2176b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2177:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2177b
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
2178:
	mov eax, DWORD PTR [ebp+496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2178b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2179:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+424], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2179b
	mov eax, 0
	mov DWORD PTR [edi+452], eax
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
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2181:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2181b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2182:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2182b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 24
	mov ebp, edi
2183:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+4224], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 28
	cmp ebp, edx
	jne 2183b
	mov eax, 0
	mov ebp, edi
2184:
	mov DWORD PTR [ebp+4252], eax
	add ebp, 4
	mov edx, edi
	add edx, 228
	cmp ebp, edx
	jne 2184b
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
2185:
	mov eax, DWORD PTR [ebp+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2185b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 252
	mov ebp, edi
2186:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2664], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2186b
	mov eax, 0
	mov ebp, edi
2187:
	mov DWORD PTR [ebp+4224], eax
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2187b
	mov eax, 1
	mov DWORD PTR [edi+4224], eax
	mov ecx, 0
	mov ebp, edi
2188:
	mov eax, DWORD PTR [ebp+2664]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+4224]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2188b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2189:
	mov eax, DWORD PTR [ebp+4224]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2664]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 256
	cmp ebp, edx
	jne 2189b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2166f
2165:
	mov eax, 0
2166:
27:
	jmp 23f
22:
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2190:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2190b
	mov eax, 0
	mov ebp, edi
2191:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2191b
	mov eax, -2147483648
	mov DWORD PTR [edi+2300], eax
	mov ecx, 0
	mov ebp, edi
2192:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2192b
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
2193:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2193b
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov ebp, edi
2194:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2194b
	mov eax, -2147483648
	mov DWORD PTR [edi+528], eax
	mov ecx, 0
	mov ebp, edi
2195:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2195b
	mov eax, ecx
	xor eax, -1
	mov ebx, eax
	mov eax, 0
	mov ebp, edi
2196:
	mov DWORD PTR [ebp+512], eax
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2196b
	mov eax, 1
	mov DWORD PTR [edi+532], eax
	mov ecx, 0
	mov ebp, edi
2197:
	mov eax, DWORD PTR [ebp+64]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+512]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2197b
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
	je 2198f
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2200:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2200b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2201:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2201b
	mov ecx, 0
	mov ebp, edi
2202:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2202b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2203:
	or ecx, DWORD PTR [ebp+1384]
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2203b
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
2204:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2204b
	mov eax, 2
	mov DWORD PTR [edi+1912], eax
	mov ecx, 0
	mov ebp, edi
2205:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1912]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2205b
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
2206:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2206b
	mov eax, 0
	mov ebp, edi
2207:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2207b
	mov eax, 1
	mov DWORD PTR [edi+1912], eax
	mov ecx, 0
	mov ebp, edi
2208:
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
	jne 2208b
	mov esi, edi
	add esi, 14944
	mov ecx, -1
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2209:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2209b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2210:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2210b
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
2211:
	mov eax, DWORD PTR [ebp+400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2211b
	mov esi, edi
	add esi, 14816
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2212:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+344], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2212b
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov ecx, 0
	mov ebp, edi
2213:
	or ecx, DWORD PTR [ebp+344]
	add ebp, 4
	mov edx, edi
	add edx, 24
	cmp ebp, edx
	jne 2213b
	mov edx, ecx
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov esi, DWORD PTR [edi+8192]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2214:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+64], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2214b
	mov esi, DWORD PTR [edi+8200]
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2215:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2215b
	mov esi, DWORD PTR [edi+8196]
	mov ebx, esi
	add ebx, 16
	mov ebp, edi
2216:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+2176], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 20
	cmp ebp, edx
	jne 2216b
	mov eax, 0
	mov ebp, edi
2217:
	mov DWORD PTR [ebp+2196], eax
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 2217b
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
2218:
	mov eax, DWORD PTR [ebp+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2218b
	mov esi, edi
	add esi, 14944
	mov ebx, esi
	add ebx, 124
	mov ebp, edi
2219:
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+1384], eax
	sub ebx, 4
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2219b
	mov eax, 0
	mov ebp, edi
2220:
	mov DWORD PTR [ebp+2176], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2220b
	mov eax, 1
	mov DWORD PTR [edi+2176], eax
	mov ecx, 0
	mov ebp, edi
2221:
	mov eax, DWORD PTR [ebp+1384]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+2176]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2221b
	mov eax, ecx
	mov ebx, eax
	mov ecx, 0
	mov ebp, edi
2222:
	mov eax, DWORD PTR [ebp+2176]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+1384]
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 2222b
	mov eax, ecx
	or eax, ebx
	xor eax, -1
	mov edx, eax
	mov eax, DWORD PTR [edi+8244]
	and eax, edx
	mov DWORD PTR [edi+8244], eax
	mov eax, DWORD PTR [edi+8244]
	and eax, 1
	jmp 2199f
2198:
	mov eax, 0
2199:
23:
	mov ebx, DWORD PTR [edi+8256]
	mov ebp, DWORD PTR [edi+8260]
	mov esi, DWORD PTR [edi+8264]
	mov edi, DWORD PTR [edi+8268]
	ret
	.p2align 6
