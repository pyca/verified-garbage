// The functions of `src/internal/vg_mldsa44_sign_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_core:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
	mov eax, DWORD PTR [esi+1104]
	test eax, eax
	jne 20f
	mov eax, DWORD PTR [esp+20]
	add eax, 128
	mov ecx, 96
	mov edx, 2
	mov ebx, 2
	mov edi, esi
	add edi, 26624
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
	add eax, 26624
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
	add edi, 27648
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
	add eax, 27648
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
	add edi, 28672
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
	add eax, 28672
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
	add edi, 29696
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
	add eax, 29696
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
	add edi, 30720
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
	add eax, 30720
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
	add edi, 31744
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
	add eax, 31744
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
	add edi, 32768
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
	add eax, 32768
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
	add edi, 33792
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
	add eax, 33792
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 34816
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
	add eax, 34816
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 35840
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
	add eax, 35840
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 36864
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
	add eax, 36864
	mov ecx, esi
	add ecx, 3072
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
	mov edi, esi
	add edi, 37888
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
	add eax, 37888
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov eax, 1
	mov DWORD PTR [esi+840], eax
	mov edi, DWORD PTR [esp+20]
	add edi, 0
	mov ebp, esi
	add ebp, 856
	mov ecx, 8
22:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 22b
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 0
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 38912
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
	add ecx, 39936
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
	add ecx, 40960
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
	add ecx, 41984
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
	add ecx, 43008
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
	add ecx, 44032
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
	add ecx, 45056
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
	add ecx, 46080
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
	add ecx, 47104
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
	add ecx, 48128
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
	add ecx, 49152
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
	add ecx, 50176
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
	add ecx, 51200
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
	add ecx, 52224
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
	add ecx, 53248
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
	add ecx, 54272
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
	jne 23f
	jmp 24f
23:
	mov edi, DWORD PTR [esp+20]
	add edi, 32
	mov ebp, esi
	add ebp, 896
	mov ecx, 8
25:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 25b
	mov edi, DWORD PTR [esp+28]
	add edi, 0
	mov ebp, esi
	add ebp, 928
	mov ecx, 8
26:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 26b
	mov edx, esi
	add edx, 0
	mov eax, 0
	mov ecx, 50
27:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 27b
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
28:
	mov eax, DWORD PTR [esi+848]
	add eax, 0
	mov BYTE PTR [esi+1024], al
	shr eax, 8
	mov BYTE PTR [esi+1025], al
	mov eax, esi
	add eax, 960
	mov ecx, 131072
	mov edx, esi
	add edx, 14336
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
	add edi, 14336
	mov ebp, esi
	add ebp, 18432
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 18432
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
	mov ecx, 131072
	mov edx, esi
	add edx, 15360
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
	add edi, 15360
	mov ebp, esi
	add ebp, 19456
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 19456
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
	mov ecx, 131072
	mov edx, esi
	add edx, 16384
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
	add edi, 16384
	mov ebp, esi
	add ebp, 20480
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 20480
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
	mov ecx, 131072
	mov edx, esi
	add edx, 17408
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
	add edi, 17408
	mov ebp, esi
	add ebp, 21504
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 21504
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, esi
	add ecx, 38912
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
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
	add eax, 22528
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
	add eax, 22528
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
	add eax, 22528
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
	add ecx, 43008
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, esi
	add ecx, 44032
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
	add eax, 23552
	mov ecx, esi
	add ecx, 45056
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
	add eax, 23552
	mov ecx, esi
	add ecx, 46080
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
	add eax, 23552
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
	add ecx, 47104
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
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
	add eax, 24576
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
	add eax, 24576
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
	add eax, 24576
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 51200
	mov edx, esi
	add edx, 18432
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 52224
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
	add eax, 25600
	mov ecx, esi
	add ecx, 53248
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
	add eax, 25600
	mov ecx, esi
	add ecx, 54272
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
	add eax, 25600
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, 95232
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
	mov ecx, 43
	mov edx, esi
	add edx, 2048
	mov ebx, 192
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
	add eax, 23552
	mov ecx, 95232
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
	mov ecx, 43
	mov edx, esi
	add edx, 2240
	mov ebx, 192
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
	add eax, 24576
	mov ecx, 95232
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
	mov ecx, 43
	mov edx, esi
	add edx, 2432
	mov ebx, 192
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
	add eax, 25600
	mov ecx, 95232
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
	mov ecx, 43
	mov edx, esi
	add edx, 2624
	mov ebx, 192
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
213:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 213b
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
	mov ebp, 768
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
	mov edx, 16
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
	mov ebp, 32
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
	mov ecx, 32
	mov edx, 39
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
	jne 214f
	mov eax, 0
	mov DWORD PTR [esi+840], eax
	mov eax, 1
	mov DWORD PTR [esi+844], eax
	jmp 215f
214:
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
	add edx, 26624
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
	add eax, 14336
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 14336
	mov ecx, 130994
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
	jne 216f
	jmp 217f
216:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 27648
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
	add eax, 15360
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 15360
	mov ecx, 130994
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
	jne 218f
	jmp 219f
218:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 28672
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
	add eax, 16384
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 16384
	mov ecx, 130994
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
	jne 220f
	jmp 221f
220:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 29696
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
	add eax, 17408
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_add}
	pop eax
	pop eax
	mov eax, esi
	add eax, 17408
	mov ecx, 130994
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
	jne 222f
	jmp 223f
222:
223:
221:
219:
217:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 224f
	jmp 225f
224:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 30720
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
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 22528
	mov ecx, 95232
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
	mov ecx, 95154
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
	jne 226f
	jmp 227f
226:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 31744
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
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 23552
	mov ecx, 95232
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
	mov ecx, 95154
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
	jne 228f
	jmp 229f
228:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 32768
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
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 24576
	mov ecx, 95232
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
	mov ecx, 95154
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
	jne 230f
	jmp 231f
230:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 33792
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
	add eax, 25600
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 25600
	mov ecx, 95232
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
	mov ecx, 95154
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
	jne 232f
	jmp 233f
232:
233:
231:
229:
227:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 234f
	jmp 235f
234:
	mov eax, esi
	add eax, 8192
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 34816
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
	mov ecx, 95232
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 22528
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
236:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 236b
	mov eax, esi
	add eax, 22528
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
	add ecx, 22528
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 22528
	mov edx, 95232
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
	add edx, 35840
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
	mov ecx, 95232
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 23552
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
237:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 237b
	mov eax, esi
	add eax, 23552
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
	add ecx, 23552
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 23552
	mov edx, 95232
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
	add edx, 36864
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
	mov ecx, 95232
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 24576
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
238:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 238b
	mov eax, esi
	add eax, 24576
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
	add ecx, 24576
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 24576
	mov edx, 95232
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
	add edx, 37888
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
	mov ecx, 95232
	push ecx
	push eax
	call {vg_mldsa_norm_lt}
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
	mov edi, esi
	add edi, 25600
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
239:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 239b
	mov eax, esi
	add eax, 25600
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
	add ecx, 25600
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 25600
	mov edx, 95232
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
	mov eax, DWORD PTR [esi+852]
	sub eax, 81
	shr eax, 31
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
235:
225:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 240f
	mov eax, DWORD PTR [esi+848]
	add eax, 4
	mov DWORD PTR [esi+848], eax
	jmp 241f
240:
	mov eax, 1
	mov DWORD PTR [esi+844], eax
241:
215:
	mov eax, DWORD PTR [esi+844]
	sub eax, 1
	mov DWORD PTR [esi+844], eax
	jne 28b
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 242f
	jmp 243f
242:
	mov edi, esi
	add edi, 1040
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 8
244:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 244b
	mov eax, esi
	add eax, 14336
	mov ecx, 131071
	mov edx, 131072
	mov ebx, DWORD PTR [esp+32]
	add ebx, 32
	mov edi, 576
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
	add eax, 15360
	mov ecx, 131071
	mov edx, 131072
	mov ebx, DWORD PTR [esp+32]
	add ebx, 608
	mov edi, 576
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
	add eax, 16384
	mov ecx, 131071
	mov edx, 131072
	mov ebx, DWORD PTR [esp+32]
	add ebx, 1184
	mov edi, 576
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
	add eax, 17408
	mov ecx, 131071
	mov edx, 131072
	mov ebx, DWORD PTR [esp+32]
	add ebx, 1760
	mov edi, 576
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
	mov ecx, 1024
	mov edx, 80
	mov ebx, DWORD PTR [esp+32]
	add ebx, 2336
	mov edi, 84
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
243:
24:
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
