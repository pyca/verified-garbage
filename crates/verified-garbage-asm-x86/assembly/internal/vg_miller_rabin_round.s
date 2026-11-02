// The functions of `src/internal/vg_miller_rabin_round.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	push ebx
	push ebp
	push esi
	push edi
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov edx, DWORD PTR [edi+224]
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, edi
	add ebx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
20:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 20b
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
21:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 21b
	mov ebp, DWORD PTR [edi+112]
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
22:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 22b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
23:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 23b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
24:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 24b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
25:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 25b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
26:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 26b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
27:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 27b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
28:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 28b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
29:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 29b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
210:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 210b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
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
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
212:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 212b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
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
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
214:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 214b
	mov eax, 5
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
	add ebp, edx
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
215:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 215b
	mov eax, 5
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
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+112]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
216:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 216b
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+224]
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, edi
	add ebx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
217:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 217b
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov DWORD PTR [edi+232], esi
	mov eax, 0
	mov DWORD PTR [edi+184], eax
218:
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov eax, DWORD PTR [edi+232]
	sub eax, 1
	add eax, eax
	add eax, eax
	add ebp, eax
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [edi+208], eax
	mov eax, 8
	mov DWORD PTR [edi+240], eax
219:
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 4
	mov DWORD PTR [edi+236], eax
220:
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
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+224]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, edi
	add ecx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ebx, 0
221:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ecx]
	or ebx, eax
	add ebp, 4
	add ecx, 4
	sub esi, 1
	jne 221b
	mov eax, 0
	sub ebx, 1
	adc eax, 0
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+244]
	sub edx, eax
	shr edx, 31
	mov ecx, DWORD PTR [edi+12]
	and ecx, edx
	mov edx, DWORD PTR [edi+184]
	or edx, ecx
	mov DWORD PTR [edi+184], edx
	sub eax, 1
	mov DWORD PTR [edi+236], eax
	jne 220b
	mov ebp, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+224]
	mov ebx, 0
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, ebx
	add ebx, edx
	add ebx, ebx
	add ebx, edx
	add ebx, edi
	add ebx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
222:
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	add ebx, 4
	add ebp, 4
	sub esi, 1
	jne 222b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 1
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
223:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 223b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 2
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
224:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 224b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 3
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
225:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 225b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 4
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
226:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 226b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 5
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
227:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 227b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 6
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
228:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 228b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 7
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
229:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 229b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 8
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
230:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 230b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 9
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
231:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 231b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 10
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
232:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 232b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 11
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
233:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 233b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 12
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
234:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 234b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 13
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
235:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 235b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 14
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
236:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 236b
	mov eax, DWORD PTR [edi+208]
	shr eax, 28
	xor eax, 15
	sub eax, 1
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edi
	add ebp, 256
	mov ebx, DWORD PTR [edi+104]
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ecx, DWORD PTR [edi+8]
237:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebx]
	and eax, ecx
	xor eax, DWORD PTR [ebx]
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub esi, 1
	jne 237b
	mov eax, 5
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
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+224]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, edi
	add ecx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ebx, 0
238:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ecx]
	or ebx, eax
	add ebp, 4
	add ecx, 4
	sub esi, 1
	jne 238b
	mov eax, 0
	sub ebx, 1
	adc eax, 0
	mov DWORD PTR [edi+8], eax
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+224]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, edi
	add ecx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ebx, 0
239:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ecx]
	or ebx, eax
	add ebp, 4
	add ecx, 4
	sub esi, 1
	jne 239b
	mov eax, 0
	sub ebx, 1
	adc eax, 0
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov edx, eax
	shr edx, 28
	sub edx, 1
	shr edx, 31
	mov ebx, edx
	xor ebx, 1
	mov ecx, DWORD PTR [edi+8]
	or ecx, DWORD PTR [edi+12]
	and ecx, ebx
	and edx, DWORD PTR [edi+184]
	or ecx, edx
	mov DWORD PTR [edi+184], ecx
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+240]
	sub eax, 1
	mov DWORD PTR [edi+240], eax
	jne 219b
	mov eax, DWORD PTR [edi+232]
	sub eax, 1
	mov DWORD PTR [edi+232], eax
	jne 218b
	mov edx, DWORD PTR [edi+224]
	mov ebp, 0
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, ebp
	add ebp, edx
	add ebp, ebp
	add ebp, edx
	add ebp, edi
	add ebp, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov eax, esi
	add eax, eax
	add eax, eax
	add ebp, eax
	mov eax, DWORD PTR [ebp]
	or eax, DWORD PTR [ebp+4]
	mov edx, eax
	shr edx, 16
	or eax, edx
	mov edx, eax
	shr edx, 8
	or eax, edx
	mov edx, eax
	shr edx, 4
	or eax, edx
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov ebx, eax
	shr ebx, 2
	and ebx, 1
	shr eax, 3
	and eax, 1
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, ebx
	add eax, ebx
	mov DWORD PTR [edi+244], eax
	mov eax, 3
	mov DWORD PTR [edi+236], eax
240:
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
	mov ebp, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+224]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, ecx
	add ecx, edx
	add ecx, ecx
	add ecx, edi
	add ecx, 256
	mov esi, DWORD PTR [edi+48]
	add esi, esi
	mov ebx, 0
241:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ecx]
	or ebx, eax
	add ebp, 4
	add ecx, 4
	sub esi, 1
	jne 241b
	mov eax, 0
	sub ebx, 1
	adc eax, 0
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+244]
	sub edx, eax
	shr edx, 31
	mov ecx, DWORD PTR [edi+12]
	and ecx, edx
	mov edx, DWORD PTR [edi+184]
	or edx, ecx
	mov DWORD PTR [edi+184], edx
	sub eax, 1
	mov DWORD PTR [edi+236], eax
	jne 240b
	mov eax, DWORD PTR [edi+184]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
