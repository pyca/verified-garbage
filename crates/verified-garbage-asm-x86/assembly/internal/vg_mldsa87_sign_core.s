// The functions of `src/internal/vg_mldsa87_sign_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_sign_core:
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
29:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 29b
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
210:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 210b
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
211:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 211b
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
212:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 212b
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
213:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 213b
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
214:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 214b
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
215:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 215b
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
216:
	mov DWORD PTR [edx], eax
	add edx, 4
	sub ecx, 1
	jne 216b
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
	jne 217f
	mov eax, 0
	mov DWORD PTR [esi+840], eax
	mov eax, 1
	mov DWORD PTR [esi+844], eax
	jmp 218f
217:
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
	jne 219f
	jmp 220f
219:
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
	jne 221f
	jmp 222f
221:
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
	jne 223f
	jmp 224f
223:
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
	jne 225f
	jmp 226f
225:
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
	jne 227f
	jmp 228f
227:
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
	jne 229f
	jmp 230f
229:
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
	jne 231f
	jmp 232f
231:
232:
230:
228:
226:
224:
222:
220:
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
	jne 235f
	jmp 236f
235:
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
	jne 237f
	jmp 238f
237:
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
	jne 239f
	jmp 240f
239:
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
	jne 241f
	jmp 242f
241:
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
	jne 243f
	jmp 244f
243:
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
	jne 245f
	jmp 246f
245:
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
	jne 247f
	jmp 248f
247:
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
	jne 249f
	jmp 250f
249:
250:
248:
246:
244:
242:
240:
238:
236:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 251f
	jmp 252f
251:
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
253:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 253b
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
254:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 254b
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
255:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 255b
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
256:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 256b
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
257:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 257b
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
258:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 258b
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
259:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 259b
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
260:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 260b
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
252:
234:
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 261f
	mov eax, DWORD PTR [esi+848]
	add eax, 7
	mov DWORD PTR [esi+848], eax
	jmp 262f
261:
	mov eax, 1
	mov DWORD PTR [esi+844], eax
262:
218:
	mov eax, DWORD PTR [esi+844]
	sub eax, 1
	mov DWORD PTR [esi+844], eax
	jne 28b
	mov eax, DWORD PTR [esi+840]
	test eax, eax
	jne 263f
	jmp 264f
263:
	mov edi, esi
	add edi, 1040
	mov ebp, DWORD PTR [esp+32]
	add ebp, 0
	mov ecx, 16
265:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 265b
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
264:
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
