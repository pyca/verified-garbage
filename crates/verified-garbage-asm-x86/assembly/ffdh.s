// The functions of `src/ffdh.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_check_domain:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	mov ebx, edi
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_FFDH_VETTED_GROUPS_X86}
	pop ecx
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [esp+12]
	cmp eax, 256
	je 20f
	mov ebp, 1
	jmp 21f
20:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 8
	mov ebp, 0
22:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 22b
21:
	test ebp, ebp
	je 23f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 256
	je 25f
	mov ebp, 1
	jmp 26f
25:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 784
	mov ebp, 0
27:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
26:
	test ebp, ebp
	je 28f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 384
	je 210f
	mov ebp, 1
	jmp 211f
210:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 1560
	mov ebp, 0
212:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 212b
211:
	test ebp, ebp
	je 213f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 384
	je 215f
	mov ebp, 1
	jmp 216f
215:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 2720
	mov ebp, 0
217:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
216:
	test ebp, ebp
	je 218f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 512
	je 220f
	mov ebp, 1
	jmp 221f
220:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 3880
	mov ebp, 0
222:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 222b
221:
	test ebp, ebp
	je 223f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 512
	je 225f
	mov ebp, 1
	jmp 226f
225:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 5424
	mov ebp, 0
227:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 227b
226:
	test ebp, ebp
	je 228f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 768
	je 230f
	mov ebp, 1
	jmp 231f
230:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 6968
	mov ebp, 0
232:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 232b
231:
	test ebp, ebp
	je 233f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 768
	je 235f
	mov ebp, 1
	jmp 236f
235:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 9280
	mov ebp, 0
237:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 237b
236:
	test ebp, ebp
	je 238f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 1024
	je 240f
	mov ebp, 1
	jmp 241f
240:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 11592
	mov ebp, 0
242:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 242b
241:
	test ebp, ebp
	je 243f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 1024
	je 245f
	mov ebp, 1
	jmp 246f
245:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 14672
	mov ebp, 0
247:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 247b
246:
	test ebp, ebp
	je 248f
	mov eax, 0
	jmp 249f
248:
	mov eax, 400
249:
	jmp 244f
243:
	mov eax, 400
244:
	jmp 239f
238:
	mov eax, 375
239:
	jmp 234f
233:
	mov eax, 375
234:
	jmp 229f
228:
	mov eax, 325
229:
	jmp 224f
223:
	mov eax, 325
224:
	jmp 219f
218:
	mov eax, 275
219:
	jmp 214f
213:
	mov eax, 275
214:
	jmp 29f
28:
	mov eax, 225
29:
	jmp 24f
23:
	mov eax, 225
24:
	mov ebp, DWORD PTR [ebx+36]
	mov esi, DWORD PTR [ebx+40]
	mov edi, DWORD PTR [ebx+44]
	mov ebx, DWORD PTR [ebx+32]
	test eax, eax
	jne 250f
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+72], eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	movzx eax, BYTE PTR [esi]
	mov ebx, esi
	add ebx, ecx
	sub ebx, 1
	movzx edx, BYTE PTR [ebx]
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov ebp, ecx
	sub ebp, 64
	ror ebp, 24
	add ebp, eax
	sub ebp, 128
	shr ebp, 31
	and edx, 1
	xor edx, 1
	or ebx, edx
	or ebx, ebp
	cmp ebx, 0
	je 252f
	mov eax, 0
	jmp 253f
252:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
254:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 254b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
255:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 255b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
256:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 256b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
257:
	cmp edx, 32
	jae 258f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 259f
258:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
259:
	cmp edx, 0
	jne 257b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
260:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 260b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
261:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 261b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
262:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 262b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
263:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 263b
	and ecx, DWORD PTR [edi+12]
	test ecx, ecx
	je 264f
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 266f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
268:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 268b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
269:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 269b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
270:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 270b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 2
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
271:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 271b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
272:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 272b
	and ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov eax, DWORD PTR [eax]
	and eax, 1
	mov edx, 0
	sub edx, eax
	and ecx, edx
	test ecx, ecx
	je 273f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
275:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 275b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
276:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 276b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
277:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 277b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
278:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 278b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
279:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 279b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
280:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 280b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
281:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
282:
	cmp edx, 32
	jae 283f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 284f
283:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
284:
	cmp edx, 0
	jne 282b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
285:
	cmp edx, 32
	jae 286f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 287f
286:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
287:
	cmp edx, 0
	jne 285b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
288:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 288b
	and edi, 15
	jne 289f
	jmp 290f
289:
291:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 291b
290:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 281b
	mov esi, 6
292:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 292b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
293:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 293b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
294:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 294b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
295:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 295b
	mov ebx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
296:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 296b
	or ecx, ebx
	xor ecx, -1
	test ecx, ecx
	je 297f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
299:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 299b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2100:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2100b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2101:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2101b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2102:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2102b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2103:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2103b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2104:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2104b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
2105:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2106:
	cmp edx, 32
	jae 2107f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2108f
2107:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2108:
	cmp edx, 0
	jne 2106b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2109:
	cmp edx, 32
	jae 2110f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2111f
2110:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2111:
	cmp edx, 0
	jne 2109b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2112:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2112b
	and edi, 15
	jne 2113f
	jmp 2114f
2113:
2115:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2115b
2114:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2105b
	mov esi, 6
2116:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 2116b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2117:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2117b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2118:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2118b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2119:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2119b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2120:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2120b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2121:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2121b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
2122:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2123:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2123b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 2122b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2124:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2125:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 2125b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2126:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2127:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2127b
	and edi, 15
	jne 2128f
	jmp 2129f
2128:
2130:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2130b
2129:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 2126b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 2124b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2131:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2131b
	mov ebx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2132:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2132b
	or ecx, ebx
	xor ecx, -1
	mov eax, ecx
	and eax, 1
	jmp 298f
297:
	mov eax, 0
298:
	jmp 274f
273:
	mov eax, 0
274:
	jmp 267f
266:
	mov eax, 1
267:
	jmp 265f
264:
	mov eax, 0
265:
253:
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	jmp 251f
250:
	mov eax, 1
251:
	ret
	.p2align 6

vg_ffdh_check_public:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+72], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
20:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 22b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
23:
	cmp edx, 32
	jae 24f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 25f
24:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
25:
	cmp edx, 0
	jne 23b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
26:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 26b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	add esi, ecx
	sub esi, 1
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
28:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 28b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
29:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 29b
	and ecx, DWORD PTR [edi+12]
	test ecx, ecx
	je 210f
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 212f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
214:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 214b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
216:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 216b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
217:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 217b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
218:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 218b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
219:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 219b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
220:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 220b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
221:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 221b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
222:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
223:
	cmp edx, 32
	jae 224f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 225f
224:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
225:
	cmp edx, 0
	jne 223b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
226:
	cmp edx, 32
	jae 227f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 228f
227:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
228:
	cmp edx, 0
	jne 226b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
229:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 229b
	and edi, 15
	jne 230f
	jmp 231f
230:
232:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 232b
231:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 222b
	mov esi, 6
233:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 233b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
234:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 234b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
235:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 235b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
236:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 236b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
237:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 237b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
238:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 238b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
239:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
240:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 240b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 239b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
241:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
242:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 242b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
243:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
244:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 244b
	and edi, 15
	jne 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 247b
246:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 243b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 241b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
248:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 248b
	mov ebx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
249:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 249b
	or ecx, ebx
	xor ecx, -1
	mov eax, ecx
	and eax, 1
	jmp 213f
212:
	mov eax, 1
213:
	jmp 211f
210:
	mov eax, 0
211:
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_check_private:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+72], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
20:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 22b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
23:
	cmp edx, 32
	jae 24f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 25f
24:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
25:
	cmp edx, 0
	jne 23b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
26:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 26b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
28:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 28b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	add esi, ecx
	sub esi, 1
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
210:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 210b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	add esi, ecx
	sub esi, 1
211:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 211b
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 212f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
214:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 214b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	mov ecx, -1
	mov DWORD PTR [edi+8], ecx
	jmp 213f
212:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
216:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 216b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
217:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 217b
	mov DWORD PTR [edi+8], ecx
213:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
218:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 218b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
219:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 219b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
220:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 220b
	and ecx, DWORD PTR [edi+12]
	and ecx, DWORD PTR [edi+8]
	test ecx, ecx
	je 221f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
223:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 223b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
224:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 224b
	and ecx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+8], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
225:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 225b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 226b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
227:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 227b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
228:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 228b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
229:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 229b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
230:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 230b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
231:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
232:
	cmp edx, 32
	jae 233f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 234f
233:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
234:
	cmp edx, 0
	jne 232b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
235:
	cmp edx, 32
	jae 236f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 237f
236:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
237:
	cmp edx, 0
	jne 235b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
238:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 238b
	and edi, 15
	jne 239f
	jmp 240f
239:
241:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 241b
240:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 231b
	mov esi, 6
242:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 242b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 243b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
244:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 244b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov ecx, DWORD PTR [esp+48]
	sub ebx, ecx
	mov esi, DWORD PTR [esp+44]
	add esi, ecx
	sub esi, 1
245:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 245b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
246:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 246b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
247:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 247b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
248:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 248b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
249:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
250:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 250b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 249b
	mov esi, DWORD PTR [esp+48]
	add esi, esi
251:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
252:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 252b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
253:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
254:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 254b
	and edi, 15
	jne 255f
	jmp 256f
255:
257:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 257b
256:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 253b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 251b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
258:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 258b
	mov ebx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
259:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 259b
	or ecx, ebx
	xor ecx, -1
	and ecx, DWORD PTR [edi+8]
	mov eax, ecx
	and eax, 1
	jmp 222f
221:
	mov eax, 2
222:
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_exchange:
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+72], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
20:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 22b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
23:
	cmp edx, 32
	jae 24f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 25f
24:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
25:
	cmp edx, 0
	jne 23b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
26:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 26b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
27:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 27b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
28:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 28b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
29:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 29b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
210:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 210b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
211:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 211b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
212:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
213:
	cmp edx, 32
	jae 214f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 215f
214:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
215:
	cmp edx, 0
	jne 213b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
216:
	cmp edx, 32
	jae 217f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 218f
217:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
218:
	cmp edx, 0
	jne 216b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
219:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 219b
	and edi, 15
	jne 220f
	jmp 221f
220:
222:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 222b
221:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 212b
	mov esi, 6
223:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 223b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
224:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 224b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	add esi, ecx
	sub esi, 1
225:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 225b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 226b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov ecx, DWORD PTR [esp+48]
	sub ebx, ecx
	mov esi, DWORD PTR [esp+44]
	add esi, ecx
	sub esi, 1
227:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 227b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
228:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 228b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
229:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 229b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
230:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 230b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
231:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
232:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 232b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 231b
	mov esi, DWORD PTR [esp+48]
	add esi, esi
233:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
234:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 234b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
235:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
236:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 236b
	and edi, 15
	jne 237f
	jmp 238f
237:
239:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 239b
238:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 235b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 233b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
240:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 240b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
241:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 241b
	and ecx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+8], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
242:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 242b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
243:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 243b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
244:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 244b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_derive_public:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+72], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
20:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 22b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
23:
	cmp edx, 32
	jae 24f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 25f
24:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
25:
	cmp edx, 0
	jne 23b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
26:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 26b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
28:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 28b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+44]
	mov ecx, DWORD PTR [esp+48]
	add esi, ecx
	sub esi, 1
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 210f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
212:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 212b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 213b
	mov ecx, -1
	mov DWORD PTR [edi+8], ecx
	jmp 211f
210:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
214:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 214b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
215:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 215b
	mov DWORD PTR [edi+8], ecx
211:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
216:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 216b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
217:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 217b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
218:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 218b
	and ecx, DWORD PTR [edi+12]
	and ecx, DWORD PTR [edi+8]
	test ecx, ecx
	je 219f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
221:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 221b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
222:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 222b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
223:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 223b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
224:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 224b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
225:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 225b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 226b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
227:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
228:
	cmp edx, 32
	jae 229f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 230f
229:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
230:
	cmp edx, 0
	jne 228b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
231:
	cmp edx, 32
	jae 232f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 233f
232:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
233:
	cmp edx, 0
	jne 231b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
234:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 234b
	and edi, 15
	jne 235f
	jmp 236f
235:
237:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 237b
236:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 227b
	mov esi, 6
238:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 238b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
239:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 239b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
240:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 240b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov ecx, DWORD PTR [esp+48]
	sub ebx, ecx
	mov esi, DWORD PTR [esp+44]
	add esi, ecx
	sub esi, 1
241:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 241b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
242:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 242b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
243:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 243b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
244:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 244b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
245:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
246:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 246b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 245b
	mov esi, DWORD PTR [esp+48]
	add esi, esi
247:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
248:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 248b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
249:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
250:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 250b
	and edi, 15
	jne 251f
	jmp 252f
251:
253:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 253b
252:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 249b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 247b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
254:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 254b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
255:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 255b
	and ecx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+8], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
256:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 256b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
257:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 257b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
258:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 258b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	add eax, eax
	mov ecx, 3
	sub ecx, eax
	mov eax, ecx
	jmp 220f
219:
	mov ecx, 0
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
259:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 259b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
260:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 260b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	mov eax, 2
220:
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_key_generation_init:
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov edx, 0
	cmp eax, 64
	sbb edx, edx
	xor edx, -1
	cmp eax, 1025
	sbb eax, eax
	and edx, eax
	and edx, 1
	test edx, edx
	je 20f
	mov edx, DWORD PTR [esp+8]
	mov eax, 128
	mov DWORD PTR [ecx], eax
	mov eax, 128
	mov DWORD PTR [ecx+8], eax
	mov eax, edx
	mov DWORD PTR [ecx+16], eax
	mov eax, edx
	mov DWORD PTR [ecx+24], eax
	mov eax, 0
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+28], eax
	mov eax, 1
	jmp 21f
20:
	mov eax, 0
	mov DWORD PTR [ecx], eax
	mov eax, 0
	mov DWORD PTR [ecx+8], eax
	mov eax, 0
	mov DWORD PTR [ecx+16], eax
	mov eax, 0
	mov DWORD PTR [ecx+24], eax
	mov eax, 0
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+28], eax
	mov eax, 0
21:
	ret
	.p2align 6

vg_ffdh_generate_key_precompute:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+88]
	mov ecx, DWORD PTR [esp+96]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+72], eax
	mov ebx, edi
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_FFDH_VETTED_GROUPS_X86}
	pop ecx
	mov DWORD PTR [ebx+16], eax
	lea esp, [esp-16]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+12]
	cmp eax, 256
	je 20f
	mov ebp, 1
	jmp 21f
20:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 8
	mov ebp, 0
22:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 22b
21:
	test ebp, ebp
	je 23f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 256
	je 25f
	mov ebp, 1
	jmp 26f
25:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 784
	mov ebp, 0
27:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
26:
	test ebp, ebp
	je 28f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 384
	je 210f
	mov ebp, 1
	jmp 211f
210:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 1560
	mov ebp, 0
212:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 212b
211:
	test ebp, ebp
	je 213f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 384
	je 215f
	mov ebp, 1
	jmp 216f
215:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 2720
	mov ebp, 0
217:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
216:
	test ebp, ebp
	je 218f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 512
	je 220f
	mov ebp, 1
	jmp 221f
220:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 3880
	mov ebp, 0
222:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 222b
221:
	test ebp, ebp
	je 223f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 512
	je 225f
	mov ebp, 1
	jmp 226f
225:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 5424
	mov ebp, 0
227:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 227b
226:
	test ebp, ebp
	je 228f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 768
	je 230f
	mov ebp, 1
	jmp 231f
230:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 6968
	mov ebp, 0
232:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 232b
231:
	test ebp, ebp
	je 233f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 768
	je 235f
	mov ebp, 1
	jmp 236f
235:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 9280
	mov ebp, 0
237:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 237b
236:
	test ebp, ebp
	je 238f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 1024
	je 240f
	mov ebp, 1
	jmp 241f
240:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 11592
	mov ebp, 0
242:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 242b
241:
	test ebp, ebp
	je 243f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 1024
	je 245f
	mov ebp, 1
	jmp 246f
245:
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebx+16]
	add edi, 14672
	mov ebp, 0
247:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 247b
246:
	test ebp, ebp
	je 248f
	mov eax, 0
	jmp 249f
248:
	mov eax, 400
249:
	jmp 244f
243:
	mov eax, 400
244:
	jmp 239f
238:
	mov eax, 375
239:
	jmp 234f
233:
	mov eax, 375
234:
	jmp 229f
228:
	mov eax, 325
229:
	jmp 224f
223:
	mov eax, 325
224:
	jmp 219f
218:
	mov eax, 275
219:
	jmp 214f
213:
	mov eax, 275
214:
	jmp 29f
28:
	mov eax, 225
29:
	jmp 24f
23:
	mov eax, 225
24:
	lea esp, [esp+16]
	mov edi, ebx
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [esp+52]
	mov ecx, DWORD PTR [esp+16]
	sub eax, ecx
	sub eax, ecx
	mov esi, DWORD PTR [esp+12]
	add esi, eax
	add esi, eax
	mov ebx, DWORD PTR [esp+16]
	sub ebx, 1
	mov ecx, 0
	mov eax, 0
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
250:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	add edx, -1
	sbb edx, edx
	mov ebp, DWORD PTR [edi+20]
	xor ebp, -1
	and ebp, edx
	or edx, DWORD PTR [edi+20]
	mov DWORD PTR [edi+20], edx
	mov edx, ebx
	xor edx, ecx
	and edx, ebp
	xor ebx, edx
	mov edx, DWORD PTR [edi+16]
	xor eax, edx
	and eax, ebp
	xor edx, eax
	mov DWORD PTR [edi+16], edx
	add esi, 1
	add ecx, 1
	mov edx, DWORD PTR [esp+16]
	cmp ecx, edx
	jne 250b
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+16]
	mov edx, eax
	shr edx, 1
	or eax, edx
	mov edx, eax
	shr edx, 2
	or eax, edx
	mov edx, eax
	shr edx, 4
	or eax, edx
	mov DWORD PTR [edi+28], eax
	mov eax, 0
	mov ecx, DWORD PTR [edi+28]
251:
	add eax, 1
	shr ecx, 1
	test ecx, ecx
	jne 251b
	mov ecx, DWORD PTR [esp+16]
	sub ecx, 1
	sub ecx, DWORD PTR [edi+24]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add eax, ecx
	mov edx, DWORD PTR [edi+48]
	test edx, edx
	je 252f
	cmp edx, eax
	jb 254f
	jmp 255f
254:
	mov eax, edx
255:
	jmp 253f
252:
253:
	mov DWORD PTR [edi+52], eax
	mov ecx, DWORD PTR [esp+56]
	mov DWORD PTR [ecx], eax
	mov edx, eax
	add edx, 7
	shr edx, 3
	mov DWORD PTR [ecx+8], edx
	add eax, 4
	mov edx, 52429
	mul edx
	shr eax, 18
	mov DWORD PTR [edi+56], eax
	mov ecx, DWORD PTR [esp+56]
	mov DWORD PTR [ecx+16], eax
	mov eax, 0
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+20], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
256:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 256b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
257:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 257b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
258:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 258b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
259:
	cmp edx, 32
	jae 260f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 261f
260:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
261:
	cmp edx, 0
	jne 259b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
262:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 262b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
263:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 263b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
264:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 264b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
265:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 265b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
266:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 266b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
267:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 267b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
268:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 268b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
269:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 269b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
270:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
271:
	cmp edx, 32
	jae 272f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 273f
272:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
273:
	cmp edx, 0
	jne 271b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
274:
	cmp edx, 32
	jae 275f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 276f
275:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
276:
	cmp edx, 0
	jne 274b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
277:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 277b
	and edi, 15
	jne 278f
	jmp 279f
278:
280:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 280b
279:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 270b
	mov esi, 6
281:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 281b
	mov eax, 0
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
282:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 282b
	mov edi, DWORD PTR [esp+68]
	mov eax, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
283:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 283b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 2
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
284:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 284b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
285:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 285b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 3
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
286:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 286b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+68], eax
287:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+68]
	sub eax, 1
	mov DWORD PTR [edi+68], eax
	jne 287b
	mov eax, 4
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
288:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 288b
	mov edi, DWORD PTR [esp+68]
	mov eax, 3
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
289:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 289b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 5
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
290:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 290b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+68], eax
291:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+68]
	sub eax, 1
	mov DWORD PTR [edi+68], eax
	jne 291b
	mov eax, 6
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
292:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 292b
	mov edi, DWORD PTR [esp+68]
	mov eax, 3
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
293:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 293b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 7
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
294:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 294b
	mov edi, DWORD PTR [esp+68]
	mov eax, 4
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
295:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 295b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 8
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
296:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 296b
	mov edi, DWORD PTR [esp+68]
	mov eax, 5
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
297:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 297b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 9
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
298:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 298b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+68], eax
299:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+68]
	sub eax, 1
	mov DWORD PTR [edi+68], eax
	jne 299b
	mov eax, 10
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2100:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2100b
	mov edi, DWORD PTR [esp+68]
	mov eax, 3
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2101:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2101b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 11
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2102:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2102b
	mov edi, DWORD PTR [esp+68]
	mov eax, 4
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2103:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2103b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 12
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2104:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2104b
	mov edi, DWORD PTR [esp+68]
	mov eax, 5
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2105:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2105b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 13
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2106:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2106b
	mov edi, DWORD PTR [esp+68]
	mov eax, 6
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2107:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2107b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 14
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2108:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2108b
	mov edi, DWORD PTR [esp+68]
	mov eax, 7
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2109:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2109b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 15
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2110:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2110b
	mov edi, DWORD PTR [esp+68]
	mov eax, 8
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2111:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2111b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 16
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2112:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2112b
	mov edi, DWORD PTR [esp+68]
	mov eax, 9
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2113:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2113b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 17
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2114:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2114b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+68], eax
2115:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+68]
	sub eax, 1
	mov DWORD PTR [edi+68], eax
	jne 2115b
	mov eax, 18
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2116:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2116b
	mov edi, DWORD PTR [esp+68]
	mov eax, 3
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2117:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2117b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 19
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2118:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2118b
	mov edi, DWORD PTR [esp+68]
	mov eax, 4
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2119:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2119b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 20
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2120:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2120b
	mov edi, DWORD PTR [esp+68]
	mov eax, 5
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2121:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2121b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 21
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2122:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2122b
	mov edi, DWORD PTR [esp+68]
	mov eax, 6
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2123:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2123b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 22
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2124:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2124b
	mov edi, DWORD PTR [esp+68]
	mov eax, 7
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2125:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2125b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 23
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2126:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2126b
	mov edi, DWORD PTR [esp+68]
	mov eax, 8
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2127:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2127b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 24
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2128:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2128b
	mov edi, DWORD PTR [esp+68]
	mov eax, 9
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2129:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2129b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 25
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2130:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2130b
	mov edi, DWORD PTR [esp+68]
	mov eax, 10
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2131:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2131b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 26
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2132:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2132b
	mov edi, DWORD PTR [esp+68]
	mov eax, 11
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2133:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2133b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 27
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2134:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2134b
	mov edi, DWORD PTR [esp+68]
	mov eax, 12
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2135:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2135b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 28
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2136:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2136b
	mov edi, DWORD PTR [esp+68]
	mov eax, 13
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2137:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2137b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 29
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2138:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2138b
	mov edi, DWORD PTR [esp+68]
	mov eax, 14
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2139:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2139b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 30
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2140:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2140b
	mov edi, DWORD PTR [esp+68]
	mov eax, 15
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2141:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2141b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 31
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2142:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2142b
	mov edi, DWORD PTR [esp+68]
	mov eax, 16
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2143:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2143b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 32
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2144:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2144b
	mov edi, DWORD PTR [esp+68]
	mov eax, 17
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2145:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2145b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 33
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebx, eax
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2146:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2146b
	mov edi, DWORD PTR [esp+68]
	mov eax, 1
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_generate_key_cached:
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+36], ebp
	mov DWORD PTR [eax+40], esi
	mov DWORD PTR [eax+44], edi
	mov edi, eax
	lea esp, [esp-76]
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+96]
	mov ecx, DWORD PTR [esp+104]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+96]
	mov ecx, DWORD PTR [esp+104]
	add eax, ecx
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+96]
	mov ecx, DWORD PTR [esp+104]
	add eax, ecx
	add eax, ecx
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+72], eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	movzx eax, BYTE PTR [esi]
	mov ebx, esi
	add ebx, ecx
	sub ebx, 1
	movzx edx, BYTE PTR [ebx]
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov ebp, ecx
	sub ebp, 64
	ror ebp, 24
	add ebp, eax
	sub ebp, 128
	shr ebp, 31
	and edx, 1
	xor edx, 1
	or ebx, edx
	or ebx, ebp
	cmp ebx, 0
	je 20f
	mov eax, 0
	jmp 21f
20:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 22b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
24:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 24b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
25:
	cmp edx, 32
	jae 26f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 27f
26:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
27:
	cmp edx, 0
	jne 25b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
28:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 28b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	add esi, ecx
	sub esi, 1
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov ecx, DWORD PTR [esp+56]
	mov eax, DWORD PTR [ecx+8]
	mov edx, DWORD PTR [esp+16]
	sub edx, eax
	mov DWORD PTR [edi+24], edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov edx, DWORD PTR [ecx]
	sub edx, eax
	add edx, 8
	mov eax, 1
210:
	add eax, eax
	sub edx, 1
	jne 210b
	sub eax, 1
	mov DWORD PTR [edi+28], eax
	mov esi, DWORD PTR [esp+44]
	mov ebx, DWORD PTR [esp+4]
	mov ecx, 0
211:
	mov eax, ecx
	cmp eax, DWORD PTR [edi+24]
	sbb edx, edx
	xor eax, DWORD PTR [edi+24]
	add eax, -1
	sbb ebp, ebp
	mov eax, DWORD PTR [edi+28]
	xor eax, 255
	and eax, ebp
	xor eax, DWORD PTR [edi+28]
	xor edx, -1
	and eax, edx
	movzx edx, BYTE PTR [esi]
	and edx, eax
	mov BYTE PTR [ebx], dl
	add esi, 1
	add ebx, 1
	add ecx, 1
	mov eax, DWORD PTR [esp+16]
	cmp ecx, eax
	jne 211b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
212:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 212b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	add esi, ecx
	sub esi, 1
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 213b
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 214f
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
216:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 216b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov esi, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [esp+32]
	add esi, ecx
	sub esi, 1
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 217b
	mov ecx, -1
	mov DWORD PTR [edi+8], ecx
	jmp 215f
214:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
218:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 218b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
219:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 219b
	mov DWORD PTR [edi+8], ecx
215:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
220:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 220b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
221:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 221b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
222:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 222b
	and ecx, DWORD PTR [edi+12]
	and ecx, DWORD PTR [edi+8]
	test ecx, ecx
	je 223f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
225:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 225b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
226:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 226b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
227:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 227b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
228:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 228b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
229:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 229b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
230:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 230b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
231:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
232:
	cmp edx, 32
	jae 233f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 234f
233:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
234:
	cmp edx, 0
	jne 232b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
235:
	cmp edx, 32
	jae 236f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 237f
236:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
237:
	cmp edx, 0
	jne 235b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
238:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 238b
	and edi, 15
	jne 239f
	jmp 240f
239:
241:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 241b
240:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 231b
	mov esi, 6
242:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 242b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, DWORD PTR [esp+56]
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+68], eax
243:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 0
	mov DWORD PTR [edi+4], eax
	mov esi, DWORD PTR [edi+68]
	sub esi, 1
	mov ecx, esi
	shr ecx, 5
	add ecx, ecx
	add ecx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	cmp ecx, edx
	jb 244f
	mov eax, 0
	jmp 245f
244:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov ecx, esi
	and ecx, 31
	test ecx, 16
	jne 246f
	jmp 247f
246:
	shr eax, 16
247:
	test ecx, 8
	jne 248f
	jmp 249f
248:
	shr eax, 8
249:
	test ecx, 4
	jne 250f
	jmp 251f
250:
	shr eax, 4
251:
	test ecx, 2
	jne 252f
	jmp 253f
252:
	shr eax, 2
253:
	test ecx, 1
	jne 254f
	jmp 255f
254:
	shr eax, 1
255:
245:
	and eax, 1
	or eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+4], eax
	mov esi, DWORD PTR [edi+68]
	sub esi, 1
	add esi, DWORD PTR [edi+56]
	mov ecx, esi
	shr ecx, 5
	add ecx, ecx
	add ecx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	cmp ecx, edx
	jb 256f
	mov eax, 0
	jmp 257f
256:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov ecx, esi
	and ecx, 31
	test ecx, 16
	jne 258f
	jmp 259f
258:
	shr eax, 16
259:
	test ecx, 8
	jne 260f
	jmp 261f
260:
	shr eax, 8
261:
	test ecx, 4
	jne 262f
	jmp 263f
262:
	shr eax, 4
263:
	test ecx, 2
	jne 264f
	jmp 265f
264:
	shr eax, 2
265:
	test ecx, 1
	jne 266f
	jmp 267f
266:
	shr eax, 1
267:
257:
	and eax, 1
	add eax, eax
	or eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+4], eax
	mov esi, DWORD PTR [edi+68]
	sub esi, 1
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	mov ecx, esi
	shr ecx, 5
	add ecx, ecx
	add ecx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	cmp ecx, edx
	jb 268f
	mov eax, 0
	jmp 269f
268:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov ecx, esi
	and ecx, 31
	test ecx, 16
	jne 270f
	jmp 271f
270:
	shr eax, 16
271:
	test ecx, 8
	jne 272f
	jmp 273f
272:
	shr eax, 8
273:
	test ecx, 4
	jne 274f
	jmp 275f
274:
	shr eax, 4
275:
	test ecx, 2
	jne 276f
	jmp 277f
276:
	shr eax, 2
277:
	test ecx, 1
	jne 278f
	jmp 279f
278:
	shr eax, 1
279:
269:
	and eax, 1
	add eax, eax
	add eax, eax
	or eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+4], eax
	mov esi, DWORD PTR [edi+68]
	sub esi, 1
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	mov ecx, esi
	shr ecx, 5
	add ecx, ecx
	add ecx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	cmp ecx, edx
	jb 280f
	mov eax, 0
	jmp 281f
280:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov ecx, esi
	and ecx, 31
	test ecx, 16
	jne 282f
	jmp 283f
282:
	shr eax, 16
283:
	test ecx, 8
	jne 284f
	jmp 285f
284:
	shr eax, 8
285:
	test ecx, 4
	jne 286f
	jmp 287f
286:
	shr eax, 4
287:
	test ecx, 2
	jne 288f
	jmp 289f
288:
	shr eax, 2
289:
	test ecx, 1
	jne 290f
	jmp 291f
290:
	shr eax, 1
291:
281:
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	or eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+4], eax
	mov esi, DWORD PTR [edi+68]
	sub esi, 1
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	add esi, DWORD PTR [edi+56]
	mov ecx, esi
	shr ecx, 5
	add ecx, ecx
	add ecx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	cmp ecx, edx
	jb 292f
	mov eax, 0
	jmp 293f
292:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, ecx
	mov eax, DWORD PTR [ebp]
	mov ecx, esi
	and ecx, 31
	test ecx, 16
	jne 294f
	jmp 295f
294:
	shr eax, 16
295:
	test ecx, 8
	jne 296f
	jmp 297f
296:
	shr eax, 8
297:
	test ecx, 4
	jne 298f
	jmp 299f
298:
	shr eax, 4
299:
	test ecx, 2
	jne 2100f
	jmp 2101f
2100:
	shr eax, 2
2101:
	test ecx, 1
	jne 2102f
	jmp 2103f
2102:
	shr eax, 1
2103:
293:
	and eax, 1
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	or eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2104:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2104b
	mov eax, 2
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mul edx
	mov ecx, DWORD PTR [esp+56]
	add eax, ecx
	add eax, 24
	mov ebp, eax
	mov eax, DWORD PTR [edi+4]
	xor eax, 0
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2105:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2105b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2106:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2106b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2107:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2107b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2108:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2108b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2109:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2109b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2110:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2110b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2111:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2111b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2112:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2112b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2113:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2113b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2114:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2114b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2115:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2115b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2116:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2116b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2117:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2117b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2118:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2118b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2119:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2119b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2120:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2120b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2121:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2121b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 17
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2122:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2122b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 18
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2123:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2123b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 19
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2124:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2124b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 20
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2125:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2125b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 21
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2126:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2126b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 22
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2127:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2127b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 23
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2128:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2128b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 24
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2129:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2129b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 25
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2130:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2130b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 26
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2131:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2131b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 27
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2132:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2132b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 28
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2133:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2133b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 29
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2134:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2134b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 30
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2135:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2135b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [edi+4]
	xor eax, 31
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2136:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2136b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, DWORD PTR [edi+68]
	sub eax, 1
	mov DWORD PTR [edi+68], eax
	jne 243b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2137:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2137b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2138:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2138b
	mov DWORD PTR [edi+12], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2139:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2139b
	and ecx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+8], ecx
	mov eax, DWORD PTR [esp+52]
	sub eax, DWORD PTR [esp+16]
	sub eax, DWORD PTR [esp+16]
	je 2140f
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2142:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2142b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2143:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2143b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2144:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2144b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 3
	mov DWORD PTR [eax], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2145:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2145b
	mov edx, DWORD PTR [edi+3336]
	and edx, 1
	mov eax, 0
	sub eax, edx
	and ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2146:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2146b
	mov edi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [edi+3336]
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
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
2147:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 2147b
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov ecx, 1
	mov DWORD PTR [eax], ecx
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	mov eax, esi
	shr eax, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, eax
2148:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2149:
	cmp edx, 32
	jae 2150f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2151f
2150:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2151:
	cmp edx, 0
	jne 2149b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 0
	sub edx, ecx
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, eax
	mov ecx, 0
2152:
	cmp edx, 32
	jae 2153f
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jmp 2154f
2153:
	add ecx, ecx
	mov eax, DWORD PTR [ebp]
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [ebp+4]
	sbb eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [ebp+8]
	sbb eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [ebp+12]
	sbb eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [ebp+16]
	sbb eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [ebp+20]
	sbb eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [ebp+24]
	sbb eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [ebp+28]
	sbb eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+28], eax
	sbb ecx, ecx
	add ebp, 32
	add ebx, 32
	add edi, 32
	sub edx, 32
2154:
	cmp edx, 0
	jne 2152b
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2155:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2155b
	and edi, 15
	jne 2156f
	jmp 2157f
2156:
2158:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2158b
2157:
	mov edi, DWORD PTR [esp+68]
	sub esi, 1
	jne 2148b
	mov esi, 6
2159:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	cmp esi, 0
	jne 2159b
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2160:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2160b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2161:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2161b
	mov edi, DWORD PTR [esp+68]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2162:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2162b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2163:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2163b
	mov edi, DWORD PTR [esp+68]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2164:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2164b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add esi, edx
	add esi, edx
2165:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ebx, esi
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2166:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2166b
	mov edi, DWORD PTR [esp+68]
	mov esi, ebx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp esi, edx
	jne 2165b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
2167:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov eax, edi
	add eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add eax, edx
	sub eax, 4
	mov eax, DWORD PTR [eax]
	shr eax, 28
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2168:
	mov eax, DWORD PTR [ebp]
	mov ebx, eax
	shr ebx, 28
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	mov DWORD PTR [ebp], eax
	mov ecx, ebx
	add ebp, 4
	sub edx, 4
	jne 2168b
	mov eax, DWORD PTR [edi+4]
	add eax, 16
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
2169:
	mov eax, DWORD PTR [edi+4]
	xor eax, 16
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+4]
	sub eax, 1
	mov DWORD PTR [edi+4], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
	mov eax, edi
	shr eax, 4
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
2170:
	movdqu xmm0, XMMWORD PTR [ebx]
	movdqu xmm1, XMMWORD PTR [ebp]
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add ebp, 16
	add ebx, 16
	sub eax, 1
	jne 2170b
	and edi, 15
	jne 2171f
	jmp 2172f
2171:
2173:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2173b
2172:
	mov edi, DWORD PTR [esp+68]
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, 32
	mov edx, edi
	add edx, 3336
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	add edx, eax
	cmp ebp, edx
	jne 2169b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 2167b
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	add edx, edx
	add edx, 32
	mov eax, 3336
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 3336
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 3336
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2174:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2174b
	mov ebx, ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, 0
2175:
	mov eax, DWORD PTR [esi]
	add ecx, ecx
	sbb eax, DWORD PTR [ebp]
	sbb ecx, ecx
	add esi, 4
	add ebp, 4
	sub edx, 4
	jne 2175b
	or ecx, ebx
	xor ecx, -1
	and ecx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+8], ecx
	jmp 2141f
2140:
2141:
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2176:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2176b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
2177:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 2177b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2178:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2178b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2179:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2179b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
2180:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 2180b
	mov ebx, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2181:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2181b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	add eax, eax
	mov ecx, 3
	sub ecx, eax
	mov eax, ecx
	jmp 224f
223:
	mov ecx, 0
	mov DWORD PTR [edi+8], ecx
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2182:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2182b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
2183:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 2183b
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2184:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2184b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	mov ecx, -1
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebx, edi
	add ebx, 3336
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 7
	shr edi, 3
	add edi, edi
	add edi, edi
	add edi, edi
2185:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 2185b
	mov edi, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov ebp, edi
	add ebp, 3336
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [edi+8]
2186:
	mov eax, DWORD PTR [ebp]
	and eax, ecx
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub edx, 4
	jne 2186b
	mov ebx, DWORD PTR [esp+36]
	mov ecx, DWORD PTR [esp+40]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, 32
	mov esi, edi
	add esi, 3336
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, ecx
	sub esi, 1
2187:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 2187b
	mov eax, DWORD PTR [edi+8]
	and eax, 1
	mov eax, 2
224:
21:
	lea esp, [esp+76]
	mov ebx, DWORD PTR [edi+32]
	mov ebp, DWORD PTR [edi+36]
	mov esi, DWORD PTR [edi+40]
	mov edi, DWORD PTR [edi+44]
	ret
	.p2align 6

vg_ffdh_generate_key_search_cached:
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [eax+32], esi
	mov esi, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esi+84], eax
	mov eax, 0
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+28], eax
20:
	mov eax, DWORD PTR [esi]
	test eax, eax
	je 21f
	mov eax, DWORD PTR [esi+8]
	test eax, eax
	je 23f
	mov eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+16]
	cmp eax, ecx
	jb 25f
	lea esp, [esp-52]
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [esp+48], eax
	call {vg_ffdh_generate_key_cached}
	lea esp, [esp+52]
	mov edx, eax
	mov ecx, DWORD PTR [esi+16]
	mov eax, DWORD PTR [esi+52]
	add eax, ecx
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	sub eax, ecx
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	add eax, ecx
	mov DWORD PTR [esi+60], eax
	cmp edx, 1
	je 27f
	cmp edx, 2
	je 29f
	cmp edx, 3
	je 211f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 3
	mov DWORD PTR [esi+72], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
213:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 213b
	mov edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
214:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 214b
	jmp 212f
211:
	mov eax, DWORD PTR [esi]
	sub eax, 1
	mov DWORD PTR [esi], eax
	mov eax, 128
	mov DWORD PTR [esi+8], eax
	mov eax, 4
	mov DWORD PTR [esi+72], eax
212:
	jmp 210f
29:
	mov eax, DWORD PTR [esi+8]
	sub eax, 1
	mov DWORD PTR [esi+8], eax
	mov eax, 4
	mov DWORD PTR [esi+72], eax
210:
	jmp 28f
27:
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 1
	mov DWORD PTR [esi+72], eax
28:
	jmp 26f
25:
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esi+24], eax
	mov eax, 0
	mov DWORD PTR [esi+72], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
215:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 215b
	mov edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
216:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 216b
26:
	jmp 24f
23:
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 3
	mov DWORD PTR [esi+72], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
217:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 217b
	mov edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
218:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 218b
24:
	jmp 22f
21:
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 3
	mov DWORD PTR [esi+72], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
219:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 219b
	mov edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+16]
	mov eax, 0
220:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 220b
22:
	mov eax, DWORD PTR [esi+72]
	cmp eax, 4
	je 20b
	mov ecx, DWORD PTR [esi+76]
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [ecx], eax
	mov eax, 0
	mov DWORD PTR [ecx+4], eax
	mov eax, DWORD PTR [esi+72]
	mov esi, DWORD PTR [esi+32]
	ret
	.p2align 6

vg_ffdh_parameter_generation_init:
	mov edx, DWORD PTR [esp+8]
	cmp edx, 512
	jb 20f
	cmp edx, 8193
	jae 22f
	mov eax, DWORD PTR [esp+12]
	cmp eax, 2
	je 24f
	cmp eax, 5
	je 26f
	mov ecx, DWORD PTR [esp+4]
	mov eax, 0
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+8], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+16], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+24], eax
	mov DWORD PTR [ecx+28], eax
	jmp 27f
26:
	mov eax, DWORD PTR [esp+8]
	mul eax
	mov edx, 64
	mul edx
	mov ecx, DWORD PTR [esp+4]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	mov DWORD PTR [ecx+8], eax
	mov edx, 32769
	mul edx
	mov DWORD PTR [ecx+16], eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	mov edx, 512
	mul edx
	mov DWORD PTR [ecx+24], eax
	mov eax, 0
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+28], eax
	mov eax, 1
27:
	jmp 25f
24:
	mov eax, DWORD PTR [esp+8]
	mul eax
	mov edx, 64
	mul edx
	mov ecx, DWORD PTR [esp+4]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	mov DWORD PTR [ecx+8], eax
	mov edx, 32769
	mul edx
	mov DWORD PTR [ecx+16], eax
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	mov edx, 512
	mul edx
	mov DWORD PTR [ecx+24], eax
	mov eax, 0
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+28], eax
	mov eax, 1
25:
	jmp 23f
22:
	mov ecx, DWORD PTR [esp+4]
	mov eax, 0
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+8], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+16], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+24], eax
	mov DWORD PTR [ecx+28], eax
23:
	jmp 21f
20:
	mov ecx, DWORD PTR [esp+4]
	mov eax, 0
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+8], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+16], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+24], eax
	mov DWORD PTR [ecx+28], eax
21:
	ret
	.p2align 6

vg_ffdh_generate_parameters:
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+32], esi
	mov esi, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esi+64], eax
	mov eax, 0
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+28], eax
20:
	mov eax, DWORD PTR [esi]
	or eax, DWORD PTR [esi+4]
	test eax, eax
	je 21f
	mov eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+8]
	cmp eax, ecx
	jb 23f
	lea esp, [esp-36]
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+4], eax
	mov eax, esi
	add eax, 80
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [esp+32], eax
	call {vg_ffdh_parameter_candidate_sieved}
	lea esp, [esp+36]
	mov edx, eax
	mov ecx, DWORD PTR [esi+80]
	mov eax, DWORD PTR [esi+52]
	add eax, ecx
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	sub eax, ecx
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+72]
	add eax, ecx
	mov DWORD PTR [esi+72], eax
	cmp edx, 1
	je 25f
	cmp edx, 2
	je 27f
	mov eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+16]
	cmp eax, ecx
	jb 29f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 3
	mov DWORD PTR [esi+68], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+8]
	mov eax, 0
211:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 211b
	jmp 210f
29:
	mov eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+8]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	cmp eax, ecx
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	add eax, eax
	mov ecx, DWORD PTR [esi+16]
	cmp ecx, eax
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	mov DWORD PTR [esi+24], eax
	mov eax, 0
	mov DWORD PTR [esi+68], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+8]
	mov eax, 0
212:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 212b
210:
	jmp 28f
27:
	mov eax, DWORD PTR [esi]
	sub eax, 1
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	sbb eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, 4
	mov DWORD PTR [esi+68], eax
28:
	jmp 26f
25:
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 1
	mov DWORD PTR [esi+68], eax
26:
	jmp 24f
23:
	mov eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+8]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	cmp eax, ecx
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	add eax, eax
	mov ecx, DWORD PTR [esi+16]
	cmp ecx, eax
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	mov DWORD PTR [esi+24], eax
	mov eax, 0
	mov DWORD PTR [esi+68], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+8]
	mov eax, 0
213:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 213b
24:
	jmp 22f
21:
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], eax
	mov eax, 3
	mov DWORD PTR [esi+68], eax
	mov edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+8]
	mov eax, 0
214:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 214b
22:
	mov eax, DWORD PTR [esi+68]
	cmp eax, 4
	je 20b
	mov ecx, DWORD PTR [esi+40]
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [ecx], eax
	mov eax, 0
	mov DWORD PTR [ecx+4], eax
	mov eax, DWORD PTR [esi+68]
	mov esi, DWORD PTR [esi+32]
	ret
	.p2align 6
