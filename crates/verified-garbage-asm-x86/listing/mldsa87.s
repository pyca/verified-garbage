// The functions of `src/mldsa87.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_keygen:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, 1
	mov DWORD PTR [esi+900], eax
	mov eax, 8
	mov BYTE PTR [esi+896], al
	mov eax, 7
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
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 0
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
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 0
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
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 0
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
	mov eax, 0
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
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 1
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
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 2
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
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 2
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
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 20480
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
	add edi, 20480
	mov ecx, 256
219:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 219b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 21504
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
	add edi, 21504
	mov ecx, 256
220:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 220b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 22528
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
	add edi, 22528
	mov ecx, 256
221:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 221b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 23552
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
	add edi, 23552
	mov ecx, 256
222:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 222b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 24576
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
	add edi, 24576
	mov ecx, 256
223:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 223b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 25600
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
	add edi, 25600
	mov ecx, 256
224:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 224b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 26624
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
	add edi, 26624
	mov ecx, 256
225:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 225b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 27648
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
	add edi, 27648
	mov ecx, 256
226:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 226b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 28672
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
	add edi, 28672
	mov ecx, 256
227:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 227b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 29696
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
	add edi, 29696
	mov ecx, 256
228:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 228b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 30720
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
	add edi, 30720
	mov ecx, 256
229:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 229b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 31744
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
	add edi, 31744
	mov ecx, 256
230:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 32768
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
	add edi, 32768
	mov ecx, 256
231:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 231b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 33792
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
	add edi, 33792
	mov ecx, 256
232:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 232b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 34816
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
	add edi, 34816
	mov ecx, 256
233:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 233b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 35840
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
	add edi, 35840
	mov ecx, 256
234:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 234b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 36864
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
	add edi, 36864
	mov ecx, 256
235:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 235b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 37888
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
	add edi, 37888
	mov ecx, 256
236:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 236b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 38912
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
	add edi, 38912
	mov ecx, 256
237:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 237b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 39936
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
	add edi, 39936
	mov ecx, 256
238:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 238b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 40960
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
	add edi, 40960
	mov ecx, 256
239:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 239b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 41984
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
	add edi, 41984
	mov ecx, 256
240:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 240b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 43008
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
	add edi, 43008
	mov ecx, 256
241:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 241b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 44032
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
	add edi, 44032
	mov ecx, 256
242:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 242b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 45056
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
	add edi, 45056
	mov ecx, 256
243:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 243b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 46080
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
	add edi, 46080
	mov ecx, 256
244:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 244b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 47104
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
	add edi, 47104
	mov ecx, 256
245:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 245b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 48128
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
	add edi, 48128
	mov ecx, 256
246:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 246b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 49152
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
	add edi, 49152
	mov ecx, 256
247:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 247b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 50176
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
	add edi, 50176
	mov ecx, 256
248:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 248b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 51200
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
	add edi, 51200
	mov ecx, 256
249:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 249b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 52224
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
	add edi, 52224
	mov ecx, 256
250:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 250b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 53248
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
	add edi, 53248
	mov ecx, 256
251:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 251b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 54272
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
	add edi, 54272
	mov ecx, 256
252:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 252b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 55296
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
	add edi, 55296
	mov ecx, 256
253:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 253b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 56320
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
	add edi, 56320
	mov ecx, 256
254:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 254b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 57344
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
	add edi, 57344
	mov ecx, 256
255:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 255b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 58368
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
	add edi, 58368
	mov ecx, 256
256:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 256b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 59392
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
	add edi, 59392
	mov ecx, 256
257:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 257b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 60416
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
	add edi, 60416
	mov ecx, 256
258:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 258b
	mov eax, 0
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 61440
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
	add edi, 61440
	mov ecx, 256
259:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 259b
	mov eax, 1
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 62464
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
	add edi, 62464
	mov ecx, 256
260:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 260b
	mov eax, 2
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 63488
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
	add edi, 63488
	mov ecx, 256
261:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 261b
	mov eax, 3
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 64512
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
	add edi, 64512
	mov ecx, 256
262:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 262b
	mov eax, 4
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 65536
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
	add edi, 65536
	mov ecx, 256
263:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 263b
	mov eax, 5
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 66560
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
	add edi, 66560
	mov ecx, 256
264:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 264b
	mov eax, 6
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 67584
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
	add edi, 67584
	mov ecx, 256
265:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 265b
	mov eax, 7
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 68608
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
	add edi, 68608
	mov ecx, 256
266:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 266b
	mov eax, 8
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 69632
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
	add edi, 69632
	mov ecx, 256
267:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 267b
	mov eax, 9
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 70656
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
	add edi, 70656
	mov ecx, 256
268:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 268b
	mov eax, 10
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 71680
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
	add edi, 71680
	mov ecx, 256
269:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 269b
	mov eax, 11
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 72704
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
	add edi, 72704
	mov ecx, 256
270:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 270b
	mov eax, 12
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 73728
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
	add edi, 73728
	mov ecx, 256
271:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 271b
	mov eax, 13
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 74752
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
	add edi, 74752
	mov ecx, 256
272:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 272b
	mov eax, 14
	mov BYTE PTR [esi+1280], al
	mov eax, esi
	add eax, 1216
	mov ecx, 2
	mov edx, esi
	add edx, 75776
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
	add edi, 75776
	mov ecx, 256
273:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 273b
	mov edi, esi
	add edi, 1024
	mov ebp, DWORD PTR [esp+24]
	add ebp, 0
	mov ecx, 8
274:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 274b
	mov edi, esi
	add edi, 1024
	mov ebp, DWORD PTR [esp+28]
	add ebp, 0
	mov ecx, 8
275:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 275b
	mov edi, esi
	add edi, 1120
	mov ebp, DWORD PTR [esp+28]
	add ebp, 32
	mov ecx, 8
276:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 276b
	mov eax, esi
	add eax, 61440
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
	add eax, 62464
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
	add eax, 63488
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
	add eax, 64512
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
	add eax, 65536
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
	add eax, 66560
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
	add eax, 67584
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
	add eax, 68608
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
	add eax, 69632
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 896
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
	add eax, 70656
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 992
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
	add eax, 71680
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1088
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
	add eax, 72704
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1184
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
	add eax, 73728
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1280
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
	add eax, 74752
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1376
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
	add eax, 75776
	mov ecx, 2
	mov edx, 2
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1472
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
	add eax, 61440
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 62464
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 63488
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 64512
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 65536
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 66560
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 67584
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 4096
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 10240
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 68608
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1568
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
	add eax, 76800
	mov ecx, esi
	add ecx, 11264
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 12288
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 13312
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 14336
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 15360
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 16384
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 17408
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 69632
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 1984
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
	add eax, 76800
	mov ecx, esi
	add ecx, 18432
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 19456
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 20480
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 21504
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 22528
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 24576
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 70656
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 2400
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
	add eax, 76800
	mov ecx, esi
	add ecx, 25600
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 26624
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 27648
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 28672
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 30720
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 31744
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 71680
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 2816
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
	add eax, 76800
	mov ecx, esi
	add ecx, 32768
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 33792
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 34816
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 35840
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 36864
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 37888
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 38912
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 72704
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 1312
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 3232
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
	add eax, 76800
	mov ecx, esi
	add ecx, 39936
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 40960
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 41984
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 43008
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 44032
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 45056
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 46080
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 73728
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 1632
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 3648
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
	add eax, 76800
	mov ecx, esi
	add ecx, 47104
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 48128
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 49152
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 50176
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 51200
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 52224
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 53248
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 74752
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 1952
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 4064
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
	add eax, 76800
	mov ecx, esi
	add ecx, 54272
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 55296
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 56320
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 57344
	mov edx, esi
	add edx, 64512
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 58368
	mov edx, esi
	add edx, 65536
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 59392
	mov edx, esi
	add edx, 66560
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 60416
	mov edx, esi
	add edx, 67584
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 75776
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 76800
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 78848
	push edx
	push ecx
	push eax
	call {vg_mldsa_power2round}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 77824
	mov ecx, 1023
	mov edx, DWORD PTR [esp+24]
	add edx, 2272
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
	add eax, 78848
	mov ecx, 4095
	mov edx, 4096
	mov ebx, DWORD PTR [esp+28]
	add ebx, 4480
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
277:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 277b
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 2592
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
	mov edx, 8
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

vg_mldsa87_sign:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
	mov eax, 1
	mov DWORD PTR [esi+840], eax
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, esi
	add ebp, 856
	mov ecx, 8
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 20b
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 64512
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 65536
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 66560
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 67584
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 68608
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 69632
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 70656
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 71680
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 72704
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 73728
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 74752
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 75776
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 76800
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 78848
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 79872
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 80896
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 81920
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 82944
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 83968
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 2
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 84992
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 86016
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 87040
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 88064
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 89088
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 90112
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 91136
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 3
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 92160
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 93184
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 94208
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 95232
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 96256
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 97280
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 98304
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 4
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 99328
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 100352
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 101376
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 102400
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 103424
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 104448
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 105472
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 5
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 106496
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 107520
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 108544
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 109568
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 110592
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 111616
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 112640
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 6
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 113664
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 114688
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 115712
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 116736
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 117760
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 118784
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 5
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 119808
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, 6
	mov BYTE PTR [esi+888], al
	mov eax, 7
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 120832
	mov edx, esi
	add edx, 3072
	push edx
	push ecx
	push eax
	call {vg_mldsa_rej_ntt_poly}
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 21f
	jmp 22f
21:
	mov eax, DWORD PTR [esp+20]
	add eax, 128
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 40960
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
	mov eax, esi
	add eax, 40960
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 41984
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
	mov eax, esi
	add eax, 41984
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 43008
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
	mov eax, esi
	add eax, 43008
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 44032
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
	mov eax, esi
	add eax, 44032
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 45056
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
	mov eax, esi
	add eax, 45056
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 46080
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
	mov eax, esi
	add eax, 46080
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 47104
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
	mov eax, esi
	add eax, 47104
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 48128
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
	mov eax, esi
	add eax, 48128
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 896
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 49152
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
	mov eax, esi
	add eax, 49152
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 992
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 50176
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
	mov eax, esi
	add eax, 50176
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1088
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 51200
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
	mov eax, esi
	add eax, 51200
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1184
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 52224
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
	mov eax, esi
	add eax, 52224
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1280
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 53248
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
	mov eax, esi
	add eax, 53248
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1376
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 54272
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
	mov eax, esi
	add eax, 54272
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1472
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 55296
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
	mov eax, esi
	add eax, 55296
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1568
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 56320
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
	mov eax, esi
	add eax, 56320
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1984
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 57344
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
	mov eax, esi
	add eax, 57344
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 2400
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 58368
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
	mov eax, esi
	add eax, 58368
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 2816
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 59392
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
	mov eax, esi
	add eax, 59392
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 3232
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 60416
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
	mov eax, esi
	add eax, 60416
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 3648
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 61440
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
	mov eax, esi
	add eax, 61440
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 4064
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 62464
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
	mov eax, esi
	add eax, 62464
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 4480
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
	mov edi, esi
	add edi, 63488
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
	mov eax, esi
	add eax, 63488
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	add edi, 32
	mov ebp, esi
	add ebp, 896
	mov ecx, 8
23:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 23b
	mov edi, DWORD PTR [esp+28]
	add edi, 0
	mov ebp, esi
	add ebp, 928
	mov ecx, 8
24:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 24b
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
25:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 25b
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 896
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
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, 136
	mov edx, 64
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
	mov edx, 128
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
	add ebx, 960
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
	mov eax, 0
	mov DWORD PTR [esi+848], eax
	mov eax, 814
	mov DWORD PTR [esi+844], eax
26:
	mov eax, DWORD PTR [esi+848]
	add eax, 0
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 18432
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 18432
	mov ebp, esi
	add ebp, 25600
	mov ecx, 256
27:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 27b
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 1
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 19456
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 19456
	mov ebp, esi
	add ebp, 26624
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 28b
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 2
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 20480
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 20480
	mov ebp, esi
	add ebp, 27648
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 27648
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 3
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 21504
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 21504
	mov ebp, esi
	add ebp, 28672
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 4
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 22528
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 22528
	mov ebp, esi
	add ebp, 29696
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 29696
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 5
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 23552
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 23552
	mov ebp, esi
	add ebp, 30720
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 30720
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esi+848]
	add eax, 6
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 524288
	mov edx, esi
	add edx, 24576
	mov ebx, esi
	add ebx, 3072
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_expand_mask_poly}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 24576
	mov ebp, esi
	add ebp, 31744
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 213b
	mov eax, esi
	add eax, 31744
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 64512
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 65536
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 66560
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 67584
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 68608
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 69632
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 70656
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 71680
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 72704
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 73728
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 74752
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 75776
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 76800
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 78848
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 79872
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 80896
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 81920
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 82944
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 83968
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 84992
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 86016
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 87040
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 88064
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 89088
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 90112
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 91136
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 92160
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 93184
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 94208
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 95232
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 96256
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 97280
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 98304
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 99328
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 100352
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 101376
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 102400
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 103424
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 104448
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 105472
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 106496
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 107520
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 108544
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 109568
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 110592
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 111616
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 112640
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 113664
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 114688
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 115712
	mov edx, esi
	add edx, 26624
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 116736
	mov edx, esi
	add edx, 27648
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 117760
	mov edx, esi
	add edx, 28672
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 118784
	mov edx, esi
	add edx, 29696
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 119808
	mov edx, esi
	add edx, 30720
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 120832
	mov edx, esi
	add edx, 31744
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2048
	mov ebx, 128
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
	add eax, 33792
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2176
	mov ebx, 128
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
	add eax, 34816
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2304
	mov ebx, 128
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
	add eax, 35840
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2432
	mov ebx, 128
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
	add eax, 36864
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2560
	mov ebx, 128
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
	add eax, 37888
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2688
	mov ebx, 128
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
	add eax, 38912
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2816
	mov ebx, 128
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
	add eax, 39936
	mov ecx, 261888
	mov edx, esi
	add edx, 6144
	push edx
	push ecx
	push eax
	call {vg_mldsa_high_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, 15
	mov edx, esi
	add edx, 2944
	mov ebx, 128
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
214:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 214b
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
	mov edx, 64
	mov ebx, esi
	add ebx, 2048
	mov ebp, 1024
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
	mov edx, 0
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
	add ebx, 1040
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
	mov eax, esi
	add eax, 1040
	mov ecx, 64
	mov edx, 60
	mov ebx, esi
	add ebx, 5120
	mov edi, esi
	add edi, 3072
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_sample_in_ball}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	test eax, eax
	jne 215f
	mov eax, 0
	mov DWORD PTR [esi+840], eax
	mov eax, 1
	mov DWORD PTR [esi+844], eax
	jmp 216f
215:
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, 1
	mov DWORD PTR [esi+840], eax
	mov eax, 0
	mov DWORD PTR [esi+852], eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 40960
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 18432
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 18432
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 217f
	jmp 218f
217:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 41984
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 19456
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 19456
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 219f
	jmp 220f
219:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 43008
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 20480
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 20480
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 221f
	jmp 222f
221:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 44032
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 21504
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 21504
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 223f
	jmp 224f
223:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 45056
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 225f
	jmp 226f
225:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 46080
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 227f
	jmp 228f
227:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 47104
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 229f
	jmp 230f
229:
230:
228:
226:
224:
222:
220:
218:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 231f
	jmp 232f
231:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 48128
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 32768
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 233f
	jmp 234f
233:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 49152
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 33792
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 235f
	jmp 236f
235:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 50176
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 34816
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 237f
	jmp 238f
237:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 51200
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 35840
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 239f
	jmp 240f
239:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 52224
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 36864
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 241f
	jmp 242f
241:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 53248
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 37888
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 243f
	jmp 244f
243:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 54272
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 38912
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 245f
	jmp 246f
245:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 55296
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 39936
	mov ecx, 261888
	mov edx, esi
	add edx, 7168
	push edx
	push ecx
	push eax
	call {vg_mldsa_low_bits}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, 261768
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 247f
	jmp 248f
247:
248:
246:
244:
242:
240:
238:
236:
234:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 249f
	jmp 250f
249:
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 56320
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 32768
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
251:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 251b
	mov eax, esi
	add eax, 32768
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 32768
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 32768
	mov edx, 261888
	mov ebx, esi
	add ebx, 10240
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 57344
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 33792
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
252:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 252b
	mov eax, esi
	add eax, 33792
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 33792
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 33792
	mov edx, 261888
	mov ebx, esi
	add ebx, 11264
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 58368
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 34816
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
253:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 253b
	mov eax, esi
	add eax, 34816
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 34816
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 34816
	mov edx, 261888
	mov ebx, esi
	add ebx, 12288
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 59392
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 35840
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
254:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 254b
	mov eax, esi
	add eax, 35840
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 35840
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 35840
	mov edx, 261888
	mov ebx, esi
	add ebx, 13312
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 60416
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 36864
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
255:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 255b
	mov eax, esi
	add eax, 36864
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 36864
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 36864
	mov edx, 261888
	mov ebx, esi
	add ebx, 14336
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 61440
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 37888
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
256:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 256b
	mov eax, esi
	add eax, 37888
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 37888
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 37888
	mov edx, 261888
	mov ebx, esi
	add ebx, 15360
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 62464
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 38912
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
257:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 257b
	mov eax, esi
	add eax, 38912
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 38912
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 38912
	mov edx, 261888
	mov ebx, esi
	add ebx, 16384
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 63488
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, 261888
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 39936
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
258:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 258b
	mov eax, esi
	add eax, 39936
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 39936
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 39936
	mov edx, 261888
	mov ebx, esi
	add ebx, 17408
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_make_hint}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+852]
	add ecx, eax
	mov DWORD PTR [esi+852], ecx
	mov eax, DWORD PTR [esi+852]
	sub eax, 76
	shr eax, 31
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
250:
232:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 259f
	mov eax, DWORD PTR [esi+848]
	add eax, 7
	mov DWORD PTR [esi+848], eax
	jmp 260f
259:
	mov eax, 1
	mov DWORD PTR [esi+844], eax
260:
216:
	mov eax, DWORD PTR [esi+844]
	sub eax, 1
	mov DWORD PTR [esi+844], eax
	jne 26b
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 261f
	jmp 262f
261:
	mov edi, esi
	add edi, 1040
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 16
263:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 263b
	mov eax, esi
	add eax, 18432
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 64
	mov edi, 640
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
	add eax, 19456
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 704
	mov edi, 640
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
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 1344
	mov edi, 640
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
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 1984
	mov edi, 640
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
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 2624
	mov edi, 640
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
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 3264
	mov edi, 640
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
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 3904
	mov edi, 640
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
	add eax, 10240
	mov ecx, 2048
	mov edx, 75
	mov ebx, DWORD PTR [esp+32]
	add ebx, 4544
	mov edi, 83
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_hint_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
262:
22:
	mov eax, DWORD PTR [esi+840]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mldsa87_sign_message:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+48]
	add esi, 144384
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
	call {vg_mldsa87_sign}
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

vg_mldsa87_verify:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+28]
	add eax, 4544
	mov ecx, 83
	mov edx, 75
	mov ebx, esi
	add ebx, 8192
	mov edi, 2048
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_hint_bit_unpack}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov DWORD PTR [esi+900], eax
	mov eax, DWORD PTR [esi+900]
	test eax, eax
	jne 20f
	jmp 21f
20:
	mov eax, DWORD PTR [esp+28]
	add eax, 64
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 16384
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
	mov eax, esi
	add eax, 16384
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 704
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 17408
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
	mov eax, esi
	add eax, 17408
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 1344
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 18432
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
	mov eax, esi
	add eax, 18432
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 1984
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 19456
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
	mov eax, esi
	add eax, 19456
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 2624
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 20480
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
	mov eax, esi
	add eax, 20480
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 3264
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 21504
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
	mov eax, esi
	add eax, 21504
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esp+28]
	add eax, 3904
	mov ecx, 640
	mov edx, 524287
	mov ebx, 524288
	mov edi, esi
	add edi, 22528
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
	mov eax, esi
	add eax, 22528
	mov ecx, 524168
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
	mov eax, DWORD PTR [esi+900]
	test eax, eax
	jne 22f
	jmp 23f
22:
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, esi
	add ebp, 1152
	mov ecx, 8
24:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 24b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 28672
	mov edx, esi
	add edx, 4096
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
	add edi, 28672
	mov ecx, 256
25:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 25b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 4096
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
	add edi, 29696
	mov ecx, 256
26:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 26b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 30720
	mov edx, esi
	add edx, 4096
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
	add edi, 30720
	mov ecx, 256
27:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 27b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 31744
	mov edx, esi
	add edx, 4096
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
	add edi, 31744
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 28b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 32768
	mov edx, esi
	add edx, 4096
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
	add edi, 32768
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 33792
	mov edx, esi
	add edx, 4096
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
	add edi, 33792
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 0
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 34816
	mov edx, esi
	add edx, 4096
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
	add edi, 34816
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 36864
	mov edx, esi
	add edx, 4096
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
	add edi, 36864
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 212b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 37888
	mov edx, esi
	add edx, 4096
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
	add edi, 37888
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 38912
	mov edx, esi
	add edx, 4096
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
	add edi, 38912
	mov ecx, 256
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 39936
	mov edx, esi
	add edx, 4096
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
	add edi, 39936
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 40960
	mov edx, esi
	add edx, 4096
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
	add edi, 40960
	mov ecx, 256
216:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 216b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 41984
	mov edx, esi
	add edx, 4096
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
	add edi, 41984
	mov ecx, 256
217:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 217b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 1
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 43008
	mov edx, esi
	add edx, 4096
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
	add edi, 43008
	mov ecx, 256
218:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 218b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 45056
	mov edx, esi
	add edx, 4096
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
	add edi, 45056
	mov ecx, 256
219:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 219b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 46080
	mov edx, esi
	add edx, 4096
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
	add edi, 46080
	mov ecx, 256
220:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 220b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 47104
	mov edx, esi
	add edx, 4096
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
	add edi, 47104
	mov ecx, 256
221:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 221b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 48128
	mov edx, esi
	add edx, 4096
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
	add edi, 48128
	mov ecx, 256
222:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 222b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 49152
	mov edx, esi
	add edx, 4096
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
	add edi, 49152
	mov ecx, 256
223:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 223b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 50176
	mov edx, esi
	add edx, 4096
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
	add edi, 50176
	mov ecx, 256
224:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 224b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 2
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 51200
	mov edx, esi
	add edx, 4096
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
	add edi, 51200
	mov ecx, 256
225:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 225b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 53248
	mov edx, esi
	add edx, 4096
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
	add edi, 53248
	mov ecx, 256
226:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 226b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 54272
	mov edx, esi
	add edx, 4096
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
	add edi, 54272
	mov ecx, 256
227:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 227b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 55296
	mov edx, esi
	add edx, 4096
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
	add edi, 55296
	mov ecx, 256
228:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 228b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 56320
	mov edx, esi
	add edx, 4096
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
	add edi, 56320
	mov ecx, 256
229:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 229b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 57344
	mov edx, esi
	add edx, 4096
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
	add edi, 57344
	mov ecx, 256
230:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 230b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 58368
	mov edx, esi
	add edx, 4096
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
	add edi, 58368
	mov ecx, 256
231:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 231b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 3
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 59392
	mov edx, esi
	add edx, 4096
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
	add edi, 59392
	mov ecx, 256
232:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 232b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 61440
	mov edx, esi
	add edx, 4096
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
	add edi, 61440
	mov ecx, 256
233:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 233b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 62464
	mov edx, esi
	add edx, 4096
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
	add edi, 62464
	mov ecx, 256
234:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 234b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 63488
	mov edx, esi
	add edx, 4096
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
	add edi, 63488
	mov ecx, 256
235:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 235b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 64512
	mov edx, esi
	add edx, 4096
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
	add edi, 64512
	mov ecx, 256
236:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 236b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 65536
	mov edx, esi
	add edx, 4096
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
	add edi, 65536
	mov ecx, 256
237:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 237b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 66560
	mov edx, esi
	add edx, 4096
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
	add edi, 66560
	mov ecx, 256
238:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 238b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 4
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 67584
	mov edx, esi
	add edx, 4096
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
	add edi, 67584
	mov ecx, 256
239:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 239b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 69632
	mov edx, esi
	add edx, 4096
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
	add edi, 69632
	mov ecx, 256
240:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 240b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 70656
	mov edx, esi
	add edx, 4096
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
	add edi, 70656
	mov ecx, 256
241:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 241b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 71680
	mov edx, esi
	add edx, 4096
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
	add edi, 71680
	mov ecx, 256
242:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 242b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 72704
	mov edx, esi
	add edx, 4096
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
	add edi, 72704
	mov ecx, 256
243:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 243b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 73728
	mov edx, esi
	add edx, 4096
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
	add edi, 73728
	mov ecx, 256
244:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 244b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 74752
	mov edx, esi
	add edx, 4096
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
	add edi, 74752
	mov ecx, 256
245:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 245b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 5
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 75776
	mov edx, esi
	add edx, 4096
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
	add edi, 75776
	mov ecx, 256
246:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 246b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 4096
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
	add edi, 77824
	mov ecx, 256
247:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 247b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 78848
	mov edx, esi
	add edx, 4096
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
	add edi, 78848
	mov ecx, 256
248:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 248b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 79872
	mov edx, esi
	add edx, 4096
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
	add edi, 79872
	mov ecx, 256
249:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 249b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 80896
	mov edx, esi
	add edx, 4096
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
	add edi, 80896
	mov ecx, 256
250:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 250b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 81920
	mov edx, esi
	add edx, 4096
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
	add edi, 81920
	mov ecx, 256
251:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 251b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 82944
	mov edx, esi
	add edx, 4096
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
	add edi, 82944
	mov ecx, 256
252:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 252b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 6
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 83968
	mov edx, esi
	add edx, 4096
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
	add edi, 83968
	mov ecx, 256
253:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 253b
	mov eax, 0
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 86016
	mov edx, esi
	add edx, 4096
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
	add edi, 86016
	mov ecx, 256
254:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 254b
	mov eax, 1
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 87040
	mov edx, esi
	add edx, 4096
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
	add edi, 87040
	mov ecx, 256
255:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 255b
	mov eax, 2
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 88064
	mov edx, esi
	add edx, 4096
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
	add edi, 88064
	mov ecx, 256
256:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 256b
	mov eax, 3
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 89088
	mov edx, esi
	add edx, 4096
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
	add edi, 89088
	mov ecx, 256
257:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 257b
	mov eax, 4
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 90112
	mov edx, esi
	add edx, 4096
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
	add edi, 90112
	mov ecx, 256
258:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 258b
	mov eax, 5
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 91136
	mov edx, esi
	add edx, 4096
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
	add edi, 91136
	mov ecx, 256
259:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 259b
	mov eax, 6
	mov BYTE PTR [esi+1184], al
	mov eax, 7
	mov BYTE PTR [esi+1185], al
	mov eax, esi
	add eax, 1152
	mov ecx, esi
	add ecx, 92160
	mov edx, esi
	add edx, 4096
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
	add edi, 92160
	mov ecx, 256
260:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 260b
	mov eax, DWORD PTR [esp+28]
	add eax, 0
	mov ecx, 64
	mov edx, 60
	mov ebx, esi
	add ebx, 23552
	mov edi, esi
	add edi, 4096
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_sample_in_ball}
	pop ecx
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
261:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 261b
	mov eax, esi
	add eax, 16384
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 17408
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 18432
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 19456
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 20480
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 21504
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 28672
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 29696
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 30720
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 31744
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 32768
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 33792
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
	add eax, 26624
	mov ecx, esi
	add ecx, 34816
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 32
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2048
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 36864
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 37888
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 38912
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 39936
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 40960
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 41984
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
	add eax, 26624
	mov ecx, esi
	add ecx, 43008
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 352
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2176
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 45056
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 46080
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 47104
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 48128
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 49152
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 50176
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
	add eax, 26624
	mov ecx, esi
	add ecx, 51200
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 672
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2304
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 53248
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 54272
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 55296
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 56320
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 57344
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 58368
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
	add eax, 26624
	mov ecx, esi
	add ecx, 59392
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 992
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 11264
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2432
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 61440
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 62464
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 63488
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 64512
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 65536
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 66560
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
	add eax, 26624
	mov ecx, esi
	add ecx, 67584
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1312
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 12288
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2560
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 69632
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 70656
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 71680
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 72704
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 73728
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 74752
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
	add eax, 26624
	mov ecx, esi
	add ecx, 75776
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1632
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 13312
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2688
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 77824
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 78848
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 79872
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 80896
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 81920
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 82944
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
	add eax, 26624
	mov ecx, esi
	add ecx, 83968
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1952
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 14336
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2816
	mov ebx, 128
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
	add eax, 26624
	mov ecx, esi
	add ecx, 86016
	mov edx, esi
	add edx, 16384
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 87040
	mov edx, esi
	add edx, 17408
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 88064
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 89088
	mov edx, esi
	add edx, 19456
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 90112
	mov edx, esi
	add edx, 20480
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 91136
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
	add eax, 26624
	mov ecx, esi
	add ecx, 92160
	mov edx, esi
	add edx, 22528
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 2272
	mov ecx, esi
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 15360
	mov ecx, esi
	add ecx, 26624
	mov edx, 261888
	mov ebx, esi
	add ebx, 27648
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_use_hint}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, 15
	mov edx, esi
	add edx, 2944
	mov ebx, 128
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa_simple_bit_pack}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
262:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 262b
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
	mov edx, 64
	mov ebx, esi
	add ebx, 2048
	mov ebp, 1024
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
	mov edx, 0
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
	add ebx, 3072
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
	mov edi, esi
	add edi, 3072
	mov ebp, DWORD PTR [esp+28]
	add ebp, 0
	mov ecx, 64
	mov edx, 0
263:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [ebp]
	xor eax, ebx
	or edx, eax
	add edi, 1
	add ebp, 1
	sub ecx, 1
	jne 263b
	sub edx, 1
	sbb eax, eax
	mov ecx, DWORD PTR [esi+900]
	and ecx, eax
	mov DWORD PTR [esi+900], ecx
23:
21:
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

vg_mldsa87_verify_message:
	push ebx
	push esi
	push edi
	push ebp
	mov eax, DWORD PTR [esp+36]
	cmp eax, 256
	jae 20f
	mov esi, DWORD PTR [esp+44]
	add esi, 144384
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
	mov ebp, 2592
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
	mov edx, 8
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
	call {vg_mldsa87_verify}
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
