// The functions of `src/sha256.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -1056596264
	mov DWORD PTR [eax], ecx
	mov ecx, 914150663
	mov DWORD PTR [eax+4], ecx
	mov ecx, 812702999
	mov DWORD PTR [eax+8], ecx
	mov ecx, -150054599
	mov DWORD PTR [eax+12], ecx
	mov ecx, -4191439
	mov DWORD PTR [eax+16], ecx
	mov ecx, 1750603025
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1694076839
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1090891868
	mov DWORD PTR [eax+28], ecx
	ret
	.p2align 6

vg_sha256_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 1779033703
	mov DWORD PTR [eax], ecx
	mov ecx, -1150833019
	mov DWORD PTR [eax+4], ecx
	mov ecx, 1013904242
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1521486534
	mov DWORD PTR [eax+12], ecx
	mov ecx, 1359893119
	mov DWORD PTR [eax+16], ecx
	mov ecx, -1694144372
	mov DWORD PTR [eax+20], ecx
	mov ecx, 528734635
	mov DWORD PTR [eax+24], ecx
	mov ecx, 1541459225
	mov DWORD PTR [eax+28], ecx
	ret
	.p2align 6

vg_sha256_update:
	lea esp, [esp-636]
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+652]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+656]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebx, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+8]
	and edi, 63
20:
	test edi, edi
	je 21f
	mov eax, 64
	sub eax, edi
	cmp esi, eax
	jb 23f
	jmp 24f
23:
	mov eax, esi
24:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 25f
27:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+32], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 28f
	jmp 29f
28:
	mov eax, ebx
	add eax, 32
	mov edi, 0
	mov ecx, 1
29:
	jmp 22f
21:
	cmp esi, 64
	jae 210f
	mov eax, 64
	sub eax, edi
	cmp esi, eax
	jb 212f
	jmp 213f
212:
	mov eax, esi
213:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 214f
216:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+32], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 216b
	jmp 215f
214:
215:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 217f
	jmp 218f
217:
	mov eax, ebx
	add eax, 32
	mov edi, 0
	mov ecx, 1
218:
	jmp 211f
210:
	mov eax, ebp
	mov ecx, esi
	and ecx, 63
	mov edx, esi
	sub edx, ecx
	add ebp, edx
	mov esi, ecx
	mov ecx, edx
	shr ecx, 6
211:
22:
	test ecx, ecx
	jne 219f
	jmp 220f
219:
	mov edx, DWORD PTR [esp+24]
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 1
	test ecx, ecx
220:
	jne 20b
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+636]
	ret
	.p2align 6

vg_sha256_finalize:
	lea esp, [esp-632]
	mov eax, DWORD PTR [esp+636]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+136], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+32], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+32], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
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
	mov DWORD PTR [ebx+88], ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
29:
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, DWORD PTR [ebp+112]
	mov esi, DWORD PTR [ebp+116]
	mov edi, DWORD PTR [ebp+120]
	mov ebp, DWORD PTR [ebp+124]
	lea esp, [esp+632]
	ret
	.p2align 6

vg_sha224_finalize:
	lea esp, [esp-632]
	mov eax, DWORD PTR [esp+636]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+136], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+32], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+32], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
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
	mov DWORD PTR [ebx+88], ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
29:
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ebx, DWORD PTR [ebp+112]
	mov esi, DWORD PTR [ebp+116]
	mov edi, DWORD PTR [ebp+120]
	mov ebp, DWORD PTR [ebp+124]
	lea esp, [esp+632]
	ret
	.p2align 6

vg_sha256_update_shani:
	lea esp, [esp-636]
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+652]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+656]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebx, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+8]
	and edi, 63
20:
	test edi, edi
	je 21f
	mov eax, 64
	sub eax, edi
	cmp esi, eax
	jb 23f
	jmp 24f
23:
	mov eax, esi
24:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 25f
27:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+32], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 28f
	jmp 29f
28:
	mov eax, ebx
	add eax, 32
	mov edi, 0
	mov ecx, 1
29:
	jmp 22f
21:
	cmp esi, 64
	jae 210f
	mov eax, 64
	sub eax, edi
	cmp esi, eax
	jb 212f
	jmp 213f
212:
	mov eax, esi
213:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 214f
216:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+32], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 216b
	jmp 215f
214:
215:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 64
	je 217f
	jmp 218f
217:
	mov eax, ebx
	add eax, 32
	mov edi, 0
	mov ecx, 1
218:
	jmp 211f
210:
	mov eax, ebp
	mov ecx, esi
	and ecx, 63
	mov edx, esi
	sub edx, ecx
	add ebp, edx
	mov esi, ecx
	mov ecx, edx
	shr ecx, 6
211:
22:
	test ecx, ecx
	jne 219f
	jmp 220f
219:
	mov edx, DWORD PTR [esp+24]
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 1
	test ecx, ecx
220:
	jne 20b
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+636]
	ret
	.p2align 6

vg_sha256_finalize_shani:
	lea esp, [esp-632]
	mov eax, DWORD PTR [esp+636]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+136], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+32], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+32], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
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
	mov DWORD PTR [ebx+88], ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
29:
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, DWORD PTR [ebp+112]
	mov esi, DWORD PTR [ebp+116]
	mov edi, DWORD PTR [ebp+120]
	mov ebp, DWORD PTR [ebp+124]
	lea esp, [esp+632]
	ret
	.p2align 6

vg_sha224_finalize_shani:
	lea esp, [esp-632]
	mov eax, DWORD PTR [esp+636]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+640]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+644]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+648]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+136], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+32], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+32], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
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
	mov DWORD PTR [ebx+88], ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
29:
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ebx, DWORD PTR [ebp+112]
	mov esi, DWORD PTR [ebp+116]
	mov edi, DWORD PTR [ebp+120]
	mov ebp, DWORD PTR [ebp+124]
	lea esp, [esp+632]
	ret
	.p2align 6
