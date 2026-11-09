// The functions of `src/internal/vg_mlkem1024_encaps_h_body.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_encaps_h_body:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+40]
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, esi
	add ebp, 14284
	mov ecx, 392
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 20b
	mov edi, DWORD PTR [esp+28]
	add edi, 0
	mov ebp, esi
	add ebp, 15856
	mov ecx, 8
21:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 21b
	mov edi, DWORD PTR [esp+24]
	add edi, 0
	mov ebp, esi
	add ebp, 17528
	mov ecx, 8
22:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 22b
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
23:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 23b
	mov eax, esi
	add eax, 13312
	mov ecx, 72
	mov edx, 0
	mov ebx, esi
	add ebx, 15856
	mov ebp, 32
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 72
	mov edx, 32
	mov ebx, esi
	add ebx, 17528
	mov ebp, 32
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 72
	mov edx, 64
	mov ebx, 6
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 72
	mov edx, 0
	mov ebx, esi
	add ebx, 15888
	mov ebp, 64
	mov edi, esi
	add edi, 13512
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
	mov eax, 1
	mov DWORD PTR [esi+14280], eax
	mov eax, 0
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
24:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 24b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
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
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
25:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 25b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
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
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
26:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 26b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
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
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
27:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 27b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
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
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15852], al
	mov eax, 0
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 28b
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 10240
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15852], al
	mov eax, 1
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15852], al
	mov eax, 2
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+15852], al
	mov eax, 3
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 4
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
212:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, 11
	mov edx, esi
	add edx, 15956
	mov edi, 352
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem1024_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15852], al
	mov eax, 0
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 10240
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
	mov BYTE PTR [esi+15852], al
	mov eax, 1
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15852], al
	mov eax, 2
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+15852], al
	mov eax, 3
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
216:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 216b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 5
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
217:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 217b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, 11
	mov edx, esi
	add edx, 16308
	mov edi, 352
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem1024_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15852], al
	mov eax, 0
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
218:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 218b
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 10240
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15852], al
	mov eax, 1
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
219:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 219b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15852], al
	mov eax, 2
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
220:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 220b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+15852], al
	mov eax, 3
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
221:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 221b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 6
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
222:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 222b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, 11
	mov edx, esi
	add edx, 16660
	mov edi, 352
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem1024_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15852], al
	mov eax, 0
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
223:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 223b
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 10240
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_multiply_ntts}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15852], al
	mov eax, 1
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
224:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 224b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15852], al
	mov eax, 2
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
225:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 225b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+15852], al
	mov eax, 3
	mov BYTE PTR [esi+15853], al
	mov eax, esi
	add eax, 15820
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 11264
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+14280]
	and ecx, eax
	mov DWORD PTR [esi+14280], ecx
	mov edi, esi
	add edi, 6144
	mov ecx, 256
226:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 226b
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 6144
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 7
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
227:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 227b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, 11
	mov edx, esi
	add edx, 17012
	mov edi, 352
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem1024_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 14284
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 10240
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
	add eax, 14668
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 15052
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 15436
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 7168
	mov ecx, esi
	add ecx, 8192
	mov edx, esi
	add edx, 3072
	mov edi, esi
	add edi, 10240
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
	add eax, 5120
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 10240
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 8
	mov BYTE PTR [esi+15952], al
	mov edx, esi
	add edx, 13312
	mov eax, 0
	mov ecx, 50
228:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 228b
	mov eax, esi
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 15920
	mov ebp, 33
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 13512
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
	add eax, 13312
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14152
	mov ebp, 128
	mov edi, esi
	add edi, 13512
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
	add eax, 14152
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 15856
	mov ecx, 32
	mov edx, 1
	mov edi, esi
	add edi, 9216
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_decode_decompress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, esi
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 5120
	mov ecx, 5
	mov edx, esi
	add edx, 17364
	mov edi, 160
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem1024_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 15888
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 8
229:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 229b
	mov edi, esi
	add edi, 15956
	mov ebp, DWORD PTR [esp+36]
	add ebp, 0
	mov ecx, 392
230:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 230b
	mov eax, DWORD PTR [esi+14280]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
