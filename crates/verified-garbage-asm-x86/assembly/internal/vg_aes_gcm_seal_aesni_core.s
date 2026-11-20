// The functions of `src/internal/vg_aes_gcm_seal_aesni_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_aesni_core:
	lea esp, [esp-2604]
	mov eax, DWORD PTR [esp+2608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+36], eax
	mov eax, esp
	add eax, 44
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov esi, ebp
	add esi, 16
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+212], eax
	mov eax, 0
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+192]
	cmp eax, 12
	je 20f
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 22f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 24f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, eax
27:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
28:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 28b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 29f
	jmp 210f
29:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
210:
	jmp 25f
24:
25:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 211f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 212f
211:
212:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 213f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebp+192]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 216f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
218:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 218b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 0
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 21f
20:
	mov edi, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov DWORD PTR [esi+8], edx
	mov eax, 16777216
	mov DWORD PTR [esi+12], eax
21:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, 0
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 219f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 221f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 223f
	jmp 224f
223:
	mov ecx, eax
224:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 226f
	jmp 227f
226:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
227:
	jmp 222f
221:
222:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 228f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 230f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
232:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+152]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 233f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
235:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 235b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 234f
233:
234:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 236f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 238f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 240f
	jmp 241f
240:
	mov ecx, eax
241:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
242:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 242b
	jmp 239f
238:
239:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 243f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, esi
	add edx, 48
	add ebp, 512
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 244f
243:
244:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 245f
	mov eax, 0
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov ebx, esi
	add ebx, 64
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, esi
	add edx, 48
	add ebp, 512
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 64
	mov ecx, DWORD PTR [ebp+276]
247:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 237f
236:
237:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov eax, 0
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 248f
	mov eax, DWORD PTR [ebp+280]
	test eax, eax
	je 250f
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 252f
	jmp 253f
252:
	mov ecx, eax
253:
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+280]
	add eax, ecx
	mov DWORD PTR [ebp+280], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
254:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 254b
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	je 255f
	jmp 256f
255:
	mov ebx, esi
	add ebx, 32
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
256:
	jmp 251f
250:
251:
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 257f
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 258f
257:
258:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 259f
	mov edi, DWORD PTR [ebp+272]
	mov edx, esi
	add edx, 32
261:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 261b
	jmp 260f
259:
260:
	jmp 249f
248:
249:
	mov eax, DWORD PTR [ebp+172]
	and eax, 15
	mov DWORD PTR [ebp+280], eax
	mov ecx, DWORD PTR [ebp+280]
	test ecx, ecx
	je 262f
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov edi, esi
	add edi, 32
	mov edx, ebp
	add edx, 96
264:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 264b
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	jmp 263f
262:
263:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+188]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	add ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	bswap eax
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	add eax, 240
	mov edx, esi
	add edx, 16
	add ebp, 512
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+28]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, esi
	add ebp, 512
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+212]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2604]
	ret
	.p2align 6
