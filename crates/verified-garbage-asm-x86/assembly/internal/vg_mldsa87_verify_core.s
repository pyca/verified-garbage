// The functions of `src/internal/vg_mldsa87_verify_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_verify_core:
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 0
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 1024
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 2048
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 3072
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 4096
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 5120
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 6144
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
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 23552
	mov edx, DWORD PTR [esp+36]
	add edx, 7168
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
