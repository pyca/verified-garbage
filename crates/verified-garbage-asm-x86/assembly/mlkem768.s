// The functions of `src/mlkem768.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_check_ek:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov ecx, 384
	mov ebx, -1
20:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	mov ebp, edx
	and edx, 15
	ror edx, 24
	add eax, edx
	shr ebp, 4
	movzx edx, BYTE PTR [esi+2]
	ror edx, 28
	add ebp, edx
	sub eax, 3329
	sbb eax, eax
	and ebx, eax
	sub ebp, 3329
	sbb ebp, ebp
	and ebx, ebp
	add esi, 3
	sub ecx, 1
	jne 20b
	mov eax, ebx
	and eax, 1
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mlkem768_keygen:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, 1
	mov DWORD PTR [esi+13328], eax
	mov eax, 3
	mov BYTE PTR [esi+13192], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	add eax, 12288
	mov ecx, 72
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	add ebx, 0
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
	add ebx, 13192
	mov ebp, 1
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
	mov edx, 33
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
	add ebx, 13128
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
	mov eax, 0
	mov BYTE PTR [esi+13192], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
21:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 21b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	mov BYTE PTR [esi+13192], al
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
22:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 22b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	mov BYTE PTR [esi+13192], al
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
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	mov eax, 3
	mov BYTE PTR [esi+13192], al
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
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 4
	mov BYTE PTR [esi+13192], al
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
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 5
	mov BYTE PTR [esi+13192], al
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
	add ebx, 13160
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
	add ebx, 13200
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
	add eax, 13200
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
	add ecx, 9216
	push ecx
	push eax
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+13160], al
	mov eax, 0
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
27:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 27b
	mov eax, esi
	add eax, 6144
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
	mov eax, 1
	mov BYTE PTR [esi+13160], al
	mov eax, 0
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
28:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 28b
	mov eax, esi
	add eax, 8192
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+13160], al
	mov eax, 0
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+13160], al
	mov eax, 1
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 6144
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
	mov eax, 1
	mov BYTE PTR [esi+13160], al
	mov eax, 1
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 8192
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+13160], al
	mov eax, 1
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 8192
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, DWORD PTR [esp+24]
	add ecx, 384
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov eax, 0
	mov BYTE PTR [esi+13160], al
	mov eax, 2
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
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
	mov eax, 1
	mov BYTE PTR [esi+13160], al
	mov eax, 2
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
	mov eax, esi
	add eax, 8192
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, 2
	mov BYTE PTR [esi+13160], al
	mov eax, 2
	mov BYTE PTR [esi+13161], al
	mov eax, esi
	add eax, 13128
	mov ecx, esi
	add ecx, 7168
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
	mov ecx, DWORD PTR [esi+13328]
	and ecx, eax
	mov DWORD PTR [esi+13328], ecx
	mov edi, esi
	add edi, 7168
	mov ecx, 256
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
	mov eax, esi
	add eax, 8192
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
	add eax, 6144
	mov ecx, esi
	add ecx, 8192
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	push ecx
	push eax
	call {vg_mlkem_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 6144
	mov ecx, DWORD PTR [esp+24]
	add ecx, 768
	push ecx
	push eax
	call {vg_mlkem_encode12}
	pop eax
	pop eax
	mov edi, esi
	add edi, 13128
	mov ebp, DWORD PTR [esp+24]
	add ebp, 1152
	mov ecx, 8
216:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 216b
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
	mov edi, DWORD PTR [esp+24]
	add edi, 0
	mov ebp, DWORD PTR [esp+28]
	add ebp, 1152
	mov ecx, 296
217:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 217b
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
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 1184
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
	mov edx, 96
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
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+28]
	add ebx, 2336
	mov ebp, 32
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
	mov edi, DWORD PTR [esp+20]
	add edi, 32
	mov ebp, DWORD PTR [esp+28]
	add ebp, 2368
	mov ecx, 8
219:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [esi+13328]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_mlkem768_encaps:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
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
	mov edi, DWORD PTR [esp+24]
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
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
22:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 22b
	mov eax, esi
	add eax, 12288
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 13260
	mov ebp, 1184
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
	mov edx, 96
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
	mov ecx, 136
	mov edx, 0
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
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
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
	mov ebp, DWORD PTR [esp+28]
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
	mov ebp, DWORD PTR [esp+32]
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

vg_mlkem768_decaps:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+24]
	add eax, 0
	mov ecx, 320
	mov edx, 10
	mov edi, esi
	add edi, 5120
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
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 0
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
	add edx, 5120
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
	mov eax, DWORD PTR [esp+24]
	add eax, 320
	mov ecx, 320
	mov edx, 10
	mov edi, esi
	add edi, 5120
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
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 384
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
	add edx, 5120
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
	mov eax, DWORD PTR [esp+24]
	add eax, 640
	mov ecx, 320
	mov edx, 10
	mov edi, esi
	add edi, 5120
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
	call {vg_mlkem_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 768
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
	add edx, 5120
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
	mov eax, DWORD PTR [esp+24]
	add eax, 960
	mov ecx, 128
	mov edx, 4
	mov edi, esi
	add edi, 3072
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
	add eax, 3072
	mov ecx, esi
	add ecx, 4096
	push ecx
	push eax
	call {vg_mlkem_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 3072
	mov ecx, 1
	mov edx, esi
	add edx, 14448
	mov edi, 32
	push edi
	push edx
	push ecx
	push eax
	call {vg_mlkem_compress_encode}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	add edi, 1152
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
	mov edx, esi
	add edx, 12288
	mov eax, 0
	mov ecx, 50
21:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 21b
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
	mov ebx, DWORD PTR [esp+20]
	add ebx, 2336
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
22:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 22b
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
23:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 23b
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
25:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 25b
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
26:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 26b
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
27:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 27b
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
28:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 28b
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
29:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 29b
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
210:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 210b
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
211:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 211b
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
212:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 212b
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
213:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 213b
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
214:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 214b
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
215:
	mov eax, DWORD PTR [edi]
	and eax, edx
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 215b
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
216:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 216b
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
217:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 217b
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
	mov ebx, DWORD PTR [esp+20]
	add ebx, 2368
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
	mov ecx, 136
	mov edx, 32
	mov ebx, DWORD PTR [esp+24]
	add ebx, 0
	mov ebp, 1088
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
	mov edx, 32
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
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+24]
	mov ebp, esi
	mov ecx, 1088
	mov ebx, 0
219:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [ebp+14548]
	xor eax, edx
	or ebx, eax
	add edi, 1
	add ebp, 1
	sub ecx, 1
	jne 219b
	sub ebx, 1
	sbb ebx, ebx
	mov edi, esi
	mov ebp, DWORD PTR [esp+28]
	mov ecx, 32
220:
	movzx eax, BYTE PTR [edi+14480]
	movzx edx, BYTE PTR [edi+15640]
	xor eax, edx
	and eax, ebx
	xor eax, edx
	mov BYTE PTR [ebp], al
	add edi, 1
	add ebp, 1
	sub ecx, 1
	jne 220b
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
