// The functions of `src/mldsa44.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, 1
	mov DWORD PTR [esi+900], eax
	mov eax, 4
	mov BYTE PTR [esi+896], al
	mov eax, 4
	mov BYTE PTR [esi+897], al
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	add ebx, 0
	mov ebp, 32
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 32
	mov ebx, esi
	add ebx, 896
	mov ebp, 2
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 34
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 1024
	mov ebp, 128
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 1024
	mov ebp, esi
	add ebp, 1152
	mov ecx, 8
21:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 21b
	mov edi, esi
	add edi, 1056
	mov ebp, esi
	add ebp, 1216
	mov ecx, 16
22:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 22b
	mov eax, 0
	mov BYTE PTR [esi+1281], al
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 4096
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 4096
	mov ecx, 256
23:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 23b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
24:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 24b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
25:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 25b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
26:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 26b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 8192
	mov ecx, 256
27:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 27b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 28b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 10240
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 10240
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 11264
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 11264
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 12288
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 12288
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 13312
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 13312
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 212b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 14336
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 14336
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 15360
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 15360
	mov ecx, 256
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 16384
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 16384
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 17408
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 17408
	mov ecx, 256
216:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 18432
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 18432
	mov ecx, 256
217:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 217b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 19456
	mov edx, esi
	add edx, 2048
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 19456
	mov ecx, 256
218:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 218b
	mov eax, 0
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 20480
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 20480
	mov ecx, 256
219:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 219b
	mov eax, 1
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 21504
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 21504
	mov ecx, 256
220:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 220b
	mov eax, 2
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 22528
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 22528
	mov ecx, 256
221:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 221b
	mov eax, 3
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 23552
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 23552
	mov ecx, 256
222:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 222b
	mov eax, 4
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 24576
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 24576
	mov ecx, 256
223:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 223b
	mov eax, 5
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 25600
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 25600
	mov ecx, 256
224:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 224b
	mov eax, 6
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 26624
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 26624
	mov ecx, 256
225:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 225b
	mov eax, 7
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 27648
	mov ebx, esi
	add ebx, 2048
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_bounded_poly}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov edi, esi
	add edi, 27648
	mov ecx, 256
226:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 226b
	mov edi, esi
	add edi, 1024
	mov ebp, DWORD PTR [esp+24]
	add ebp, 0
	mov ecx, 8
227:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 227b
	mov edi, esi
	add edi, 1024
	mov ebp, DWORD PTR [esp+28]
	add ebp, 0
	mov ecx, 8
228:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 228b
	mov edi, esi
	add edi, 1120
	mov ebp, DWORD PTR [esp+28]
	add ebp, 32
	mov ecx, 8
229:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 229b
	mov eax, esi
	add eax, 20480
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 128
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 21504
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 224
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 320
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 416
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 512
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 608
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 704
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 800
	mov edi, 96
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 20480
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 21504
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 4096
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 23552
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 32
	mov ebx, 320
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 896
	mov edi, 416
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 10240
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 11264
	mov edx, esi
	add edx, 23552
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 352
	mov ebx, 320
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1312
	mov edi, 416
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 12288
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 13312
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 14336
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 15360
	mov edx, esi
	add edx, 23552
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 26624
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 672
	mov ebx, 320
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1728
	mov edi, 416
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 16384
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 17408
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 18432
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 19456
	mov edx, esi
	add edx, 23552
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 27648
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 992
	mov ebx, 320
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 2144
	mov edi, 416
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
230:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 230b
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 1312
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 88
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+28]
	add ebx, 64
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+900]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_pk_tr:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+28]
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	add ebx, 0
	mov ebp, 1312
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 88
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_prepare_verifying_key:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+28]
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, DWORD PTR [esp+24]
	add ebp, 0
	mov ecx, 328
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+20]
	add eax, 32
	mov ecx, DWORD PTR [esp+24]
	add ecx, 1312
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 1312
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 352
	mov ecx, DWORD PTR [esp+24]
	add ecx, 2336
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 2336
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 672
	mov ecx, DWORD PTR [esp+24]
	add ecx, 3360
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 3360
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 992
	mov ecx, DWORD PTR [esp+24]
	add ecx, 4384
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 4384
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_prepare_signing_key:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+28]
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, DWORD PTR [esp+24]
	add ebp, 0
	mov ecx, 640
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+20]
	add eax, 128
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 2560
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 2560
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 224
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 3584
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 3584
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 320
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 4608
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 4608
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 416
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 5632
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 5632
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 512
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 6656
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 6656
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 608
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 7680
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 7680
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 704
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 8704
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 8704
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 800
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, DWORD PTR [esp+24]
	add edi, 9728
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 9728
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 896
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, DWORD PTR [esp+24]
	add edi, 10752
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 10752
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1312
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, DWORD PTR [esp+24]
	add edi, 11776
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 11776
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1728
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, DWORD PTR [esp+24]
	add edi, 12800
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 12800
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 2144
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, DWORD PTR [esp+24]
	add edi, 13824
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_bit_unpack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+24]
	add eax, 13824
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_sign:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
	mov eax, 0
	mov DWORD PTR [esi+1104], eax
	mov eax, DWORD PTR [esp+20]
	add eax, 0
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 0
	mov ebx, DWORD PTR [esp+32]
	add ebx, 0
	mov edi, esi
	add edi, 0
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_sign_core}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_sign_message:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+48]
	add esi, 77824
	mov eax, 0
	mov BYTE PTR [esi+944], al
	mov eax, DWORD PTR [esp+36]
	mov BYTE PTR [esi+945], al
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov DWORD PTR [esi+32], eax
	mov DWORD PTR [esi+36], eax
	mov DWORD PTR [esi+40], eax
	mov DWORD PTR [esi+44], eax
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], eax
	mov DWORD PTR [esi+56], eax
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov DWORD PTR [esi+80], eax
	mov DWORD PTR [esi+84], eax
	mov DWORD PTR [esi+88], eax
	mov DWORD PTR [esi+92], eax
	mov DWORD PTR [esi+96], eax
	mov DWORD PTR [esi+100], eax
	mov DWORD PTR [esi+104], eax
	mov DWORD PTR [esi+108], eax
	mov DWORD PTR [esi+112], eax
	mov DWORD PTR [esi+116], eax
	mov DWORD PTR [esi+120], eax
	mov DWORD PTR [esi+124], eax
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], eax
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], eax
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], eax
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], eax
	mov DWORD PTR [esi+160], eax
	mov DWORD PTR [esi+164], eax
	mov DWORD PTR [esi+168], eax
	mov DWORD PTR [esi+172], eax
	mov DWORD PTR [esi+176], eax
	mov DWORD PTR [esi+180], eax
	mov DWORD PTR [esi+184], eax
	mov DWORD PTR [esi+188], eax
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], eax
	mov edx, 0
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+20]
	add ebx, 64
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 64
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, esi
	add ebx, 944
	mov ebp, 2
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 66
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+32]
	mov ebp, DWORD PTR [esp+36]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+28]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	mov ecx, esi
	add ecx, 840
	mov edx, DWORD PTR [esp+40]
	mov ebx, DWORD PTR [esp+44]
	mov edi, DWORD PTR [esp+48]
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_sign}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	jmp 21f
20:
	mov eax, 2
21:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+48]
	add esi, 77824
	mov eax, 0
	mov BYTE PTR [esi+944], al
	mov eax, DWORD PTR [esp+36]
	mov BYTE PTR [esi+945], al
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov DWORD PTR [esi+32], eax
	mov DWORD PTR [esi+36], eax
	mov DWORD PTR [esi+40], eax
	mov DWORD PTR [esi+44], eax
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], eax
	mov DWORD PTR [esi+56], eax
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov DWORD PTR [esi+80], eax
	mov DWORD PTR [esi+84], eax
	mov DWORD PTR [esi+88], eax
	mov DWORD PTR [esi+92], eax
	mov DWORD PTR [esi+96], eax
	mov DWORD PTR [esi+100], eax
	mov DWORD PTR [esi+104], eax
	mov DWORD PTR [esi+108], eax
	mov DWORD PTR [esi+112], eax
	mov DWORD PTR [esi+116], eax
	mov DWORD PTR [esi+120], eax
	mov DWORD PTR [esi+124], eax
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], eax
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], eax
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], eax
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], eax
	mov DWORD PTR [esi+160], eax
	mov DWORD PTR [esi+164], eax
	mov DWORD PTR [esi+168], eax
	mov DWORD PTR [esi+172], eax
	mov DWORD PTR [esi+176], eax
	mov DWORD PTR [esi+180], eax
	mov DWORD PTR [esi+184], eax
	mov DWORD PTR [esi+188], eax
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], eax
	mov edx, 0
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+20]
	add ebx, 64
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 64
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, esi
	add ebx, 944
	mov ebp, 2
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 66
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+32]
	mov ebp, DWORD PTR [esp+36]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+28]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	mov ecx, esi
	add ecx, 840
	mov edx, DWORD PTR [esp+40]
	mov ebx, DWORD PTR [esp+44]
	mov edi, DWORD PTR [esp+48]
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_sign_prepared}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	jmp 21f
20:
	mov eax, 2
21:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_verify:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+20]
	add eax, 32
	mov ecx, esi
	add ecx, 73728
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 73728
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 352
	mov ecx, esi
	add ecx, 74752
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 74752
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 672
	mov ecx, esi
	add ecx, 75776
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 75776
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 992
	mov ecx, esi
	add ecx, 76800
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 0
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 0
	mov ebx, esi
	add ebx, 0
	mov edi, esi
	add edi, 73728
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_verify_core}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_verify_message_cached:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+44]
	add esi, 77824
	mov eax, 0
	mov BYTE PTR [esi+944], al
	mov eax, DWORD PTR [esp+36]
	mov BYTE PTR [esi+945], al
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov DWORD PTR [esi+32], eax
	mov DWORD PTR [esi+36], eax
	mov DWORD PTR [esi+40], eax
	mov DWORD PTR [esi+44], eax
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], eax
	mov DWORD PTR [esi+56], eax
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov DWORD PTR [esi+80], eax
	mov DWORD PTR [esi+84], eax
	mov DWORD PTR [esi+88], eax
	mov DWORD PTR [esi+92], eax
	mov DWORD PTR [esi+96], eax
	mov DWORD PTR [esi+100], eax
	mov DWORD PTR [esi+104], eax
	mov DWORD PTR [esi+108], eax
	mov DWORD PTR [esi+112], eax
	mov DWORD PTR [esi+116], eax
	mov DWORD PTR [esi+120], eax
	mov DWORD PTR [esi+124], eax
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], eax
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], eax
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], eax
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], eax
	mov DWORD PTR [esi+160], eax
	mov DWORD PTR [esi+164], eax
	mov DWORD PTR [esi+168], eax
	mov DWORD PTR [esi+172], eax
	mov DWORD PTR [esi+176], eax
	mov DWORD PTR [esi+180], eax
	mov DWORD PTR [esi+184], eax
	mov DWORD PTR [esi+188], eax
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], eax
	mov edx, 0
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+48]
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 64
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, esi
	add ebx, 944
	mov ebp, 2
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 66
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+32]
	mov ebp, DWORD PTR [esp+36]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+28]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	mov ecx, esi
	add ecx, 840
	mov edx, DWORD PTR [esp+40]
	mov ebx, DWORD PTR [esp+44]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_verify}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	jmp 21f
20:
	mov eax, 2
21:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+44]
	add esi, 77824
	mov eax, 0
	mov BYTE PTR [esi+944], al
	mov eax, DWORD PTR [esp+36]
	mov BYTE PTR [esi+945], al
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], eax
	mov DWORD PTR [esi+20], eax
	mov DWORD PTR [esi+24], eax
	mov DWORD PTR [esi+28], eax
	mov DWORD PTR [esi+32], eax
	mov DWORD PTR [esi+36], eax
	mov DWORD PTR [esi+40], eax
	mov DWORD PTR [esi+44], eax
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], eax
	mov DWORD PTR [esi+56], eax
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+64], eax
	mov DWORD PTR [esi+68], eax
	mov DWORD PTR [esi+72], eax
	mov DWORD PTR [esi+76], eax
	mov DWORD PTR [esi+80], eax
	mov DWORD PTR [esi+84], eax
	mov DWORD PTR [esi+88], eax
	mov DWORD PTR [esi+92], eax
	mov DWORD PTR [esi+96], eax
	mov DWORD PTR [esi+100], eax
	mov DWORD PTR [esi+104], eax
	mov DWORD PTR [esi+108], eax
	mov DWORD PTR [esi+112], eax
	mov DWORD PTR [esi+116], eax
	mov DWORD PTR [esi+120], eax
	mov DWORD PTR [esi+124], eax
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], eax
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], eax
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], eax
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], eax
	mov DWORD PTR [esi+160], eax
	mov DWORD PTR [esi+164], eax
	mov DWORD PTR [esi+168], eax
	mov DWORD PTR [esi+172], eax
	mov DWORD PTR [esi+176], eax
	mov DWORD PTR [esi+180], eax
	mov DWORD PTR [esi+184], eax
	mov DWORD PTR [esi+188], eax
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], eax
	mov edx, 0
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+48]
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 64
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, esi
	add ebx, 944
	mov ebp, 2
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, 66
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+32]
	mov ebp, DWORD PTR [esp+36]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+28]
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov edx, eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 64
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	mov ecx, esi
	add ecx, 840
	mov edx, DWORD PTR [esp+40]
	mov ebx, DWORD PTR [esp+44]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_verify_prepared}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	jmp 21f
20:
	mov eax, 2
21:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
