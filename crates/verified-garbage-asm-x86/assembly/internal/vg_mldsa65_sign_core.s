// The functions of `src/internal/vg_mldsa65_sign_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_core:
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
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 256
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 384
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 512
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 640
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 768
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	mov eax, DWORD PTR [esp+20]
	add eax, 896
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
	mov edi, esi
	add edi, 38912
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
	add eax, 38912
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1024
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
	mov edi, esi
	add edi, 39936
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
	add eax, 39936
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1152
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 1280
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 1408
	mov ecx, 128
	mov edx, 4
	mov ebx, 4
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
	add eax, 1536
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	add eax, 1952
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	add eax, 2368
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	add eax, 2784
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	add eax, 3200
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	add eax, 3616
	mov ecx, 416
	mov edx, 4095
	mov ebx, 4096
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
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 0
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
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 0
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
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 0
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
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 0
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
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 1
	mov BYTE PTR [esi+889], al
	mov eax, esi
	add eax, 856
	mov ecx, esi
	add ecx, 55296
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
	add ecx, 56320
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
	add ecx, 57344
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
	add ecx, 58368
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
	add ecx, 59392
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
	add ecx, 60416
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
	add ecx, 61440
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
	add ecx, 62464
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
	add ecx, 63488
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
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 3
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
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 3
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
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 3
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
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 3
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
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 3
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
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 4
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
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 4
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
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 4
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
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 4
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
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 4
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
	mov eax, 0
	mov BYTE PTR [esi+888], al
	mov eax, 5
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
	mov eax, 1
	mov BYTE PTR [esi+888], al
	mov eax, 5
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
	mov eax, 2
	mov BYTE PTR [esi+888], al
	mov eax, 5
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
	mov eax, 3
	mov BYTE PTR [esi+888], al
	mov eax, 5
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
	mov eax, 4
	mov BYTE PTR [esi+888], al
	mov eax, 5
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
	mov ecx, 524288
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
	add ebp, 21504
	mov ecx, 256
29:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 29b
	mov eax, esi
	add eax, 21504
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
	add ebp, 22528
	mov ecx, 256
210:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 210b
	mov eax, esi
	add eax, 22528
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
	add ebp, 23552
	mov ecx, 256
211:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 211b
	mov eax, esi
	add eax, 23552
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
	add ebp, 24576
	mov ecx, 256
212:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 212b
	mov eax, esi
	add eax, 24576
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
	add ebp, 25600
	mov ecx, 256
213:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 213b
	mov eax, esi
	add eax, 25600
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_ntt}
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
	call {vg_mldsa_multiply_ntt}
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
	add eax, 26624
	mov ecx, esi
	add ecx, 52224
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
	add eax, 26624
	mov ecx, esi
	add ecx, 53248
	mov edx, esi
	add edx, 24576
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
	add ecx, 54272
	mov edx, esi
	add edx, 25600
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
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, esi
	add ecx, 55296
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, esi
	add ecx, 56320
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
	add eax, 27648
	mov ecx, esi
	add ecx, 57344
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
	add eax, 27648
	mov ecx, esi
	add ecx, 58368
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, esi
	add ecx, 59392
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
	mov ecx, esi
	add ecx, 60416
	mov edx, esi
	add edx, 21504
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
	add ecx, 61440
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
	add ecx, 62464
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
	add ecx, 63488
	mov edx, esi
	add edx, 24576
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
	add ecx, 64512
	mov edx, esi
	add edx, 25600
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
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, esi
	add ecx, 65536
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, esi
	add ecx, 66560
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
	add eax, 29696
	mov ecx, esi
	add ecx, 67584
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
	add eax, 29696
	mov ecx, esi
	add ecx, 68608
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, esi
	add ecx, 69632
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, esi
	add ecx, 70656
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, esi
	add ecx, 71680
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
	add eax, 30720
	mov ecx, esi
	add ecx, 72704
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
	add eax, 30720
	mov ecx, esi
	add ecx, 73728
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, esi
	add ecx, 74752
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 31744
	mov ecx, esi
	add ecx, 75776
	mov edx, esi
	add edx, 21504
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 31744
	mov ecx, esi
	add ecx, 76800
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
	add eax, 31744
	mov ecx, esi
	add ecx, 77824
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
	add eax, 31744
	mov ecx, esi
	add ecx, 78848
	mov edx, esi
	add edx, 24576
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 31744
	mov ecx, esi
	add ecx, 79872
	mov edx, esi
	add edx, 25600
	push edx
	push ecx
	push eax
	call {vg_mldsa_multiply_add_ntt}
	pop eax
	pop eax
	pop eax
	mov eax, esi
	add eax, 31744
	mov ecx, esi
	add ecx, 3072
	push ecx
	push eax
	call {vg_mldsa_inv_ntt}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
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
	add eax, 27648
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
	add eax, 28672
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
	add eax, 29696
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
	add eax, 30720
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
	add eax, 31744
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
	mov ebp, 48
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
	mov ecx, 48
	mov edx, 49
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
	mov ecx, 524092
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
	mov ecx, 524092
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
	add edx, 34816
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
	mov ecx, 524092
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
	add edx, 35840
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
	mov ecx, 524092
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
	add edx, 36864
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
	mov ecx, 524092
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
226:
224:
222:
220:
218:
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
	add edx, 37888
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
	add eax, 26624
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 26624
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
	mov ecx, 261692
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
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 38912
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
	add eax, 27648
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 27648
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
	mov ecx, 261692
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
	jne 231f
	jmp 232f
231:
	mov eax, esi
	add eax, 6144
	mov ecx, esi
	add ecx, 5120
	mov edx, esi
	add edx, 39936
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
	add eax, 28672
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 28672
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
	mov ecx, 261692
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
	add eax, 29696
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 29696
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
	mov ecx, 261692
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
	add eax, 30720
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 30720
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
	mov ecx, 261692
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
	add eax, 31744
	mov ecx, esi
	add ecx, 6144
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 31744
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
	mov ecx, 261692
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
240:
238:
236:
234:
232:
230:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 241f
	jmp 242f
241:
	mov eax, esi
	add eax, 8192
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
	add edi, 26624
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
243:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 243b
	mov eax, esi
	add eax, 26624
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
	add ecx, 26624
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 26624
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
	add edx, 45056
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
	add edi, 27648
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
244:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 244b
	mov eax, esi
	add eax, 27648
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
	add ecx, 27648
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 27648
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
	add edx, 46080
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
	add edi, 28672
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
245:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 245b
	mov eax, esi
	add eax, 28672
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
	add ecx, 28672
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 28672
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
	add edx, 47104
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
	add edi, 29696
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
246:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 246b
	mov eax, esi
	add eax, 29696
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
	add ecx, 29696
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 29696
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
	add edx, 48128
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
	add edi, 30720
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
247:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 247b
	mov eax, esi
	add eax, 30720
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
	add ecx, 30720
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 30720
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
	add edx, 49152
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
	add edi, 31744
	mov ebp, esi
	add ebp, 9216
	mov ecx, 256
248:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 248b
	mov eax, esi
	add eax, 31744
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
	add ecx, 31744
	push ecx
	push eax
	call {vg_mldsa_sub}
	pop eax
	pop eax
	mov eax, esi
	add eax, 9216
	mov ecx, esi
	add ecx, 31744
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
	mov eax, DWORD PTR [esi+852]
	sub eax, 56
	shr eax, 31
	mov ecx, DWORD PTR [esi+840]
	and ecx, eax
	mov DWORD PTR [esi+840], ecx
242:
228:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 249f
	mov eax, DWORD PTR [esi+848]
	add eax, 5
	mov DWORD PTR [esi+848], eax
	jmp 250f
249:
	mov eax, 1
	mov DWORD PTR [esi+844], eax
250:
216:
	mov eax, DWORD PTR [esi+844]
	sub eax, 1
	mov DWORD PTR [esi+844], eax
	jne 28b
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 251f
	jmp 252f
251:
	mov edi, esi
	add edi, 1040
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 12
253:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 253b
	mov eax, esi
	add eax, 16384
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 48
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
	add eax, 17408
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 688
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
	add eax, 18432
	mov ecx, 524287
	mov edx, 524288
	mov ebx, DWORD PTR [esp+32]
	add ebx, 1328
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
	add ebx, 1968
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
	add ebx, 2608
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
	mov ecx, 1536
	mov edx, 55
	mov ebx, DWORD PTR [esp+32]
	add ebx, 3248
	mov edi, 61
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
252:
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
