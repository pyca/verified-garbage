// The functions of `src/internal/vg_mlkem1024_keygen_body.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_keygen_body:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, 1
	mov DWORD PTR [esi+15376], eax
	mov eax, 4
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	add eax, 14336
	mov ecx, 72
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	add ebx, 0
	mov ebp, 32
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 72
	mov edx, 32
	mov ebx, esi
	add ebx, 15240
	mov ebp, 1
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 72
	mov edx, 33
	mov ebx, 6
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 72
	mov edx, 0
	mov ebx, esi
	add ebx, 15176
	mov ebp, 64
	mov edi, esi
	add edi, 14536
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
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
21:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 21b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 0
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
22:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 22b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 1024
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 1024
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
23:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 23b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 2048
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 2048
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
24:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 24b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 3072
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 4
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
25:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 25b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 5
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
26:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 26b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 5120
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 6
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
27:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 27b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 7
	mov BYTE PTR [esi+15240], al
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
28:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 28b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15208
	mov ebp, 33
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15248
	mov ebp, 128
	mov edi, esi
	add edi, 14536
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
	add eax, 15248
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 11264
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15208], al
	mov eax, 0
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15208], al
	mov eax, 0
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15208], al
	mov eax, 0
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15208], al
	mov eax, 0
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15208], al
	mov eax, 1
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15208], al
	mov eax, 1
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15208], al
	mov eax, 1
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15208], al
	mov eax, 1
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
216:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 216b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, DWORD PTR [esp+24]
	add ecx, 384
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15208], al
	mov eax, 2
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
217:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 217b
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15208], al
	mov eax, 2
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
218:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 218b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15208], al
	mov eax, 2
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
219:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 219b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15208], al
	mov eax, 2
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
220:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 220b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, DWORD PTR [esp+24]
	add ecx, 768
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15208], al
	mov eax, 3
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
221:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 221b
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15208], al
	mov eax, 3
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
222:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 222b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15208], al
	mov eax, 3
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
223:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 223b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15208], al
	mov eax, 3
	mov BYTE PTR [esi+15209], al
	mov eax, esi
	add eax, 15176
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 12288
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+15376]
	and ecx, eax
	mov DWORD PTR [esi+15376], ecx
	mov edi, esi
	add edi, 9216
	mov ecx, 256
224:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 224b
	mov eax, esi
	add eax, 10240
	mov ecx, esi
	add ecx, 9216
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 11264
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 8192
	mov ecx, DWORD PTR [esp+24]
	add ecx, 1152
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov edi, esi
	add edi, 15176
	mov ebp, DWORD PTR [esp+24]
	add ebp, 1536
	mov ecx, 8
225:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 225b
	mov eax, esi
	add eax, 0
	mov ecx, DWORD PTR [esp+28]
	add ecx, 0
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 1024
	mov ecx, DWORD PTR [esp+28]
	add ecx, 384
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 2048
	mov ecx, DWORD PTR [esp+28]
	add ecx, 768
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 3072
	mov ecx, DWORD PTR [esp+28]
	add ecx, 1152
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+24]
	add edi, 0
	mov ebp, DWORD PTR [esp+28]
	add ebp, 1536
	mov ecx, 392
226:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 226b
	mov edx, esi
	add edx, 14336
	mov eax, 0
	mov ecx, 50
227:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 227b
	mov eax, esi
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 1568
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 72
	mov ebx, 6
	mov edi, esi
	add edi, 14536
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
	add eax, 14336
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+28]
	add ebx, 3104
	mov ebp, 32
	mov edi, esi
	add edi, 14536
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
	mov edi, DWORD PTR [esp+20]
	add edi, 32
	mov ebp, DWORD PTR [esp+28]
	add ebp, 3136
	mov ecx, 8
228:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 228b
	mov eax, DWORD PTR [esi+15376]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
