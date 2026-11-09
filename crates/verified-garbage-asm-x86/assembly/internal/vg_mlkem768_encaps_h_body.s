// The functions of `src/internal/vg_mlkem768_encaps_h_body.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_h_body:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+40]
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, esi
	add ebp, 13260
	mov ecx, 296
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
	add ebp, 14448
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
	add ebp, 15640
	mov ecx, 8
22:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 22b
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
23:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 23b
	mov eax, esi
	add eax, 12288
	mov ecx, 72
	mov edx, 0
	mov ebx, esi
	add ebx, 14448
	mov ebp, 32
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 72
	mov edx, 32
	mov ebx, esi
	add ebx, 15640
	mov ebp, 32
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 72
	mov edx, 64
	mov ebx, 6
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 72
	mov edx, 0
	mov ebx, esi
	add ebx, 14480
	mov ebp, 64
	mov edi, esi
	add edi, 12488
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
	mov DWORD PTR [esi+13256], eax
	mov eax, 0
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
24:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 24b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
25:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 25b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
26:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 26b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+14444], al
	mov eax, 0
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
27:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 27b
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 9216
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
	mov BYTE PTR [esi+14444], al
	mov eax, 1
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 28b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+14444], al
	mov eax, 2
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 3
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
210:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, 10
	mov edx, esi
	add edx, 14548
	mov edi, 320
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+14444], al
	mov eax, 0
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 9216
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
	mov BYTE PTR [esi+14444], al
	mov eax, 1
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 1
	mov BYTE PTR [esi+14444], al
	mov eax, 2
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 4
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
214:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 214b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, 10
	mov edx, esi
	add edx, 14868
	mov edi, 320
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+14444], al
	mov eax, 0
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 9216
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
	mov BYTE PTR [esi+14444], al
	mov eax, 1
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
216:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 216b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+14444], al
	mov eax, 2
	mov BYTE PTR [esi+14445], al
	mov eax, esi
	add eax, 14412
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 10240
	push edx
	push ecx
	push eax
	call {vg_mlkem_sample_ntt}
	pop ecx
	pop ecx
	pop ecx
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esi+13256]
	and ecx, eax
	mov DWORD PTR [esi+13256], ecx
	mov edi, esi
	add edi, 5120
	mov ecx, 256
217:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 217b
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 5
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
218:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 218b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, 10
	mov edx, esi
	add edx, 15188
	mov edi, 320
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 13260
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 0
	mov edi, esi
	add edi, 9216
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
	add eax, 13644
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 1024
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 14028
	mov ecx, esi
	add ecx, 7168
	push ecx
	push eax
	call {vg_mlkem_decode12}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 7168
	mov edx, esi
	add edx, 2048
	mov edi, esi
	add edi, 9216
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
	add eax, 4096
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_inv_ntt}
	pop eax
	pop eax
	mov eax, 6
	mov BYTE PTR [esi+14544], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
219:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 219b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 14512
	mov ebp, 33
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 33
	mov ebx, 31
	mov edi, esi
	add edi, 12488
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
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13128
	mov ebp, 128
	mov edi, esi
	add edi, 12488
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
	add eax, 13128
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_cbd2}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 14448
	mov ecx, 32
	mov edx, 1
	mov edi, esi
	add edi, 8192
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
	add eax, 4096
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 4096
	mov ecx, 4
	mov edx, esi
	add edx, 15508
	mov edi, 128
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, esi
	add edi, 14480
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 8
220:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 220b
	mov edi, esi
	add edi, 14548
	mov ebp, DWORD PTR [esp+36]
	add ebp, 0
	mov ecx, 272
221:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 221b
	mov eax, DWORD PTR [esi+13256]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
