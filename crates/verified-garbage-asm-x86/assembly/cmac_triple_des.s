// The functions of `src/cmac_triple_des.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_triple_des_stream_init:
	lea esp, [esp-660]
	mov eax, DWORD PTR [esp+664]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+400], ebx
	mov ebx, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	push edx
	push eax
	push ecx
	push ebx
	push esi
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+84], ebx
	mov DWORD PTR [eax+88], esi
	mov DWORD PTR [eax+92], edi
	mov DWORD PTR [eax+96], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ecx+4]
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ecx+8]
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ecx+12]
	bswap eax
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 20f
	mov eax, DWORD PTR [ecx+16]
	mov edx, DWORD PTR [ecx+20]
	jmp 21f
20:
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
21:
	bswap eax
	bswap edx
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], edx
	mov esi, ebp
	add esi, 100
	mov edi, DWORD PTR [esp+12]
	mov edx, 3
22:
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 1025
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 262272
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 4194320
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 131076
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 1611137026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 16777216
	xor ecx, ebx
	mov DWORD PTR [edi], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 5
	and ecx, 1026
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 16640
	xor ecx, ebx
	mov DWORD PTR [edi+4], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 4
	and ecx, 8192
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 1025
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 4194320
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 131076
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 1610612738
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 1048576
	xor ecx, ebx
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 3
	and ecx, 4
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 8256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 16640
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 128
	xor ecx, ebx
	mov DWORD PTR [edi+12], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 524290
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 4194336
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 520
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 1610612736
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 41943040
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, -2147481600
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 262144
	xor ecx, ebx
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 9
	and ecx, 8192
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 32
	xor ecx, ebx
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 6144
	mov ebx, DWORD PTR [esi]
	ror ebx, 1
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 131076
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 268436480
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 1610612738
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 67141632
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 4194432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 41943040
	xor ecx, ebx
	mov DWORD PTR [edi+24], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 7
	and ecx, 16640
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 8256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 512
	xor ecx, ebx
	mov DWORD PTR [edi+28], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 1610612736
	mov ebx, DWORD PTR [esi]
	ror ebx, 1
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 48
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 41943040
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, -2147477504
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 67141632
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 8
	and ecx, 64
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 1
	xor ecx, ebx
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, -2147483648
	mov ebx, DWORD PTR [esi]
	ror ebx, 1
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 4194432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 48
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 41943040
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 268566532
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 1610612736
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 1048576
	xor ecx, ebx
	mov DWORD PTR [edi+40], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 3
	and ecx, 4096
	mov ebx, DWORD PTR [esi]
	ror ebx, 4
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 8256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 16640
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 128
	xor ecx, ebx
	mov DWORD PTR [edi+44], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 2
	mov ebx, DWORD PTR [esi]
	ror ebx, 2
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 160
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 268435460
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 1610612736
	xor ecx, ebx
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 2
	and ecx, 32
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 20
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 32768
	xor ecx, ebx
	mov DWORD PTR [edi+52], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 2
	and ecx, 256
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 268566532
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 8392704
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 4194464
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, -2147483648
	xor ecx, ebx
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 5
	and ecx, 4
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 8256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 512
	xor ecx, ebx
	mov DWORD PTR [edi+60], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 3
	and ecx, 512
	mov ebx, DWORD PTR [esi]
	ror ebx, 4
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 8392704
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, -2146435072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 268435460
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 160
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 8
	xor ecx, ebx
	mov DWORD PTR [edi+64], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 13
	and ecx, 4
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 8192
	xor ecx, ebx
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 268435456
	mov ebx, DWORD PTR [esi]
	ror ebx, 2
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 134217729
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 4
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 4194464
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 1075838976
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 33558528
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 16777216
	xor ecx, ebx
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 16384
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 256
	xor ecx, ebx
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 6
	and ecx, 2048
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 14
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 131076
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 20
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, -2113925120
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 268436480
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 32
	xor ecx, ebx
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 4
	and ecx, 512
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 64
	xor ecx, ebx
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 1024
	mov ebx, DWORD PTR [esi]
	ror ebx, 2
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 4
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 33558528
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 1610874880
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, 4194336
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 22
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 4
	xor ecx, ebx
	mov DWORD PTR [edi+88], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 2
	and ecx, 2048
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 20
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 4
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 4
	xor ecx, ebx
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 512
	mov ebx, DWORD PTR [esi]
	ror ebx, 1
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 2
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, -2113925120
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 20
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 2621440
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 16793600
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 1610612736
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 16
	xor ecx, ebx
	mov DWORD PTR [edi+96], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 2
	and ecx, 8192
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 32768
	xor ecx, ebx
	mov DWORD PTR [edi+100], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 2
	and ecx, 134217728
	mov ebx, DWORD PTR [esi]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 2621440
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 1610874880
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 4194336
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 22
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 16640
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 1025
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 18
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 16785408
	xor ecx, ebx
	mov DWORD PTR [edi+104], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 16384
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 32769
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 8
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 26
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 256
	xor ecx, ebx
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 8
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 12
	and ebx, 16640
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 19
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 1610612736
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 26
	and ebx, 262272
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 28
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 5
	and ebx, -2113929216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 7
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 134218753
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 27
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 30
	and ebx, 32
	xor ecx, ebx
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 64
	mov ebx, DWORD PTR [esi]
	ror ebx, 7
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 10
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 1
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 2
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 11
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 12
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 1026
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 32
	xor ecx, ebx
	mov DWORD PTR [edi+116], ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 1
	and ecx, 1610612736
	mov ebx, DWORD PTR [esi]
	ror ebx, 2
	and ebx, 262272
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 4
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 5
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 6
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 11
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 13
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 20
	and ebx, 8448
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 23
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 27
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 30
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	and ebx, 524290
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 3
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 6
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 13
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 21
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 24
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	and ebx, 134217729
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [esi]
	and ecx, 32
	mov ebx, DWORD PTR [esi]
	ror ebx, 9
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 15
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 18
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 29
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [esi]
	ror ebx, 31
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 10
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 14
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 19
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 20
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 23
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 28
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 29
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 31
	and ebx, 1
	xor ecx, ebx
	mov DWORD PTR [edi+124], ecx
	add edi, 128
	add esi, 8
	sub edx, 1
	jne 22b
	mov esi, DWORD PTR [esp+12]
	mov eax, 0
	mov edx, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 6
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 15
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 20
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 26
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 29
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 2
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 7
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 11
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 16
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 22
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 25
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 31
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp]
	ror ecx, 1
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 4
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 7
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 13
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 16
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 19
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 30
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 3
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 9
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 12
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 17
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 21
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 23
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 26
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov DWORD PTR [ebp+68], ecx
	mov eax, 3
	mov DWORD PTR [ebp+76], eax
	mov eax, 8
	mov DWORD PTR [ebp+80], eax
23:
	mov eax, 16
	mov DWORD PTR [ebp+72], eax
24:
	mov eax, DWORD PTR [ebp+68]
	ror eax, 25
	and eax, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 27
	and ecx, 258048
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 29
	and ecx, 4032
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 31
	and ecx, 63
	xor eax, ecx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 11
	and ecx, 258048
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 13
	and ecx, 4032
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 15
	and ecx, 63
	xor ebx, ecx
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi]
	shr ecx, 24
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+4]
	and ecx, 65535
	ror ecx, 24
	xor ebx, ecx
	mov ecx, eax
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+4], ecx
	mov ecx, eax
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+8], ecx
	mov ecx, eax
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+16], ecx
	mov ecx, eax
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, ebx
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+28], ecx
	mov ecx, ebx
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, ebx
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+36], ecx
	mov ecx, ebx
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+40], ecx
	mov ecx, ebx
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, ebx
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+48], ecx
	mov eax, DWORD PTR [ebp]
	and eax, 1598085
	xor eax, 282893
	mov ebx, DWORD PTR [ebp]
	and ebx, 3437261
	xor ebx, 1606338
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1340041
	xor ecx, 1060932
	mov ebx, DWORD PTR [ebp]
	and ebx, 3723909
	xor ebx, 2159041
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2388677
	xor edx, 3445699
	mov ebx, DWORD PTR [ebp]
	and ebx, 3699333
	xor ebx, 794639
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1372805
	xor ecx, 2908302
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461961
	xor ebx, 1315720
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 3695491
	xor edi, 524870
	mov ebx, DWORD PTR [ebp]
	and ebx, 3167173
	xor ebx, 3199372
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1601929
	xor ecx, 2400906
	mov ebx, DWORD PTR [ebp]
	and ebx, 3158729
	xor ebx, 3949383
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1864521
	xor edx, 3699465
	mov ebx, DWORD PTR [ebp]
	and ebx, 2642695
	xor ebx, 57536
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1335753
	xor ecx, 1884485
	mov ebx, DWORD PTR [ebp]
	and ebx, 3973961
	xor ebx, 2667019
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp]
	and eax, 3986249
	xor eax, 1085963
	mov ebx, DWORD PTR [ebp]
	and ebx, 840646
	xor ebx, 291086
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3723590
	xor ecx, 2159297
	mov ebx, DWORD PTR [ebp]
	and ebx, 1610499
	xor ebx, 2933640
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2929549
	xor edx, 795020
	mov ebx, DWORD PTR [ebp]
	and ebx, 2413379
	xor ebx, 3674693
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3187587
	xor ecx, 3429191
	mov ebx, DWORD PTR [ebp]
	and ebx, 3183247
	xor ebx, 565698
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 2642511
	xor edi, 3989696
	mov ebx, DWORD PTR [ebp]
	and ebx, 1339590
	xor ebx, 2622403
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1622346
	xor ecx, 1589574
	mov ebx, DWORD PTR [ebp]
	and ebx, 1626957
	xor ebx, 3158157
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1630661
	xor edx, 1343503
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461955
	xor ebx, 2413322
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3186890
	xor ecx, 45705
	mov ebx, DWORD PTR [ebp]
	and ebx, 3715530
	xor ebx, 1859652
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+24]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+20]
	xor ebx, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+56], ebx
	mov eax, DWORD PTR [ebp+28]
	and eax, 3457923
	xor eax, 3469645
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1885068
	xor ebx, 2101262
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1360460
	xor ecx, 2900555
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2642825
	xor ebx, 582085
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2380425
	xor edx, 1089920
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2904966
	xor ebx, 3961609
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3174982
	xor ecx, 1848262
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811974
	xor ebx, 295555
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 824076
	xor edi, 1593860
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2405004
	xor ebx, 1356481
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1323587
	xor ecx, 3154114
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3715654
	xor ebx, 2413452
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2384771
	xor edx, 2671431
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2380745
	xor ebx, 786570
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1630915
	xor ecx, 37128
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3994185
	xor ebx, 3694671
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, 1888454
	xor eax, 2097859
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2924742
	xor ebx, 582025
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3199558
	xor ecx, 3453062
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1335881
	xor ebx, 291392
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807369
	xor edx, 2908234
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3961219
	xor ebx, 3179463
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1594179
	xor ecx, 1102605
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2372492
	xor ebx, 1839118
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 1369033
	xor edi, 3969871
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3727820
	xor ebx, 2376196
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1339593
	xor ecx, 835845
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811980
	xor ebx, 3711179
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807366
	xor edx, 1593996
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1352652
	xor ebx, 1323329
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1622211
	xor ecx, 2630082
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2925379
	xor ebx, 62344
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+52]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+48]
	xor ebx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+60], ebx
	mov edi, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 2
	and ecx, 270336
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 7
	and ecx, 134217729
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 11
	and ecx, 136
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 16
	and ecx, 302120960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 20
	and ecx, 1048576
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 24
	and ecx, 538970112
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 27
	and ecx, 16777248
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 28
	and ecx, 1024
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 3
	and ecx, -2147483648
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 6
	and ecx, 32772
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 10
	and ecx, 4194304
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 11
	and ecx, 528
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 15
	and ecx, 1140850688
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 18
	and ecx, 2
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 23
	and ecx, 69632
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 27
	and ecx, 8912960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 30
	and ecx, 16640
	xor edi, ecx
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edi
	mov eax, DWORD PTR [ebp+80]
	add esi, eax
	mov eax, DWORD PTR [ebp+72]
	sub eax, 1
	mov DWORD PTR [ebp+72], eax
	jne 24b
	mov ecx, DWORD PTR [ebp+80]
	mov eax, 128
	sub eax, ecx
	add esi, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+76]
	sub eax, 1
	mov DWORD PTR [ebp+76], eax
	jne 23b
	sub esi, 504
	mov ecx, DWORD PTR [ebp+64]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 3
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 6
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 8
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 9
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 14
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 15
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 20
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 23
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 26
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 29
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 2
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 7
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 13
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 19
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 25
	and ebx, -2147483136
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 31
	and ebx, 2048
	xor ecx, ebx
	mov DWORD PTR [ebp], ecx
	mov ecx, DWORD PTR [ebp+64]
	ror ecx, 1
	and ecx, 1048576
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 4
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 7
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 13
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 18
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 24
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 25
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 30
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 3
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 6
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 12
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 15
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 17
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 23
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 26
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 29
	and ebx, -2147483136
	xor ecx, ebx
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+4]
	mov edi, DWORD PTR [esp+12]
	add edi, 384
	mov ecx, eax
	shr ecx, 31
	mov ebx, 0
	sub ebx, ecx
	and ebx, 27
	mov ecx, edx
	shr ecx, 31
	add eax, eax
	or eax, ecx
	add edx, edx
	xor edx, ebx
	mov ecx, eax
	bswap ecx
	mov DWORD PTR [edi], ecx
	mov ecx, edx
	bswap ecx
	mov DWORD PTR [edi+4], ecx
	mov ecx, eax
	shr ecx, 31
	mov ebx, 0
	sub ebx, ecx
	and ebx, 27
	mov ecx, edx
	shr ecx, 31
	add eax, eax
	or eax, ecx
	add edx, edx
	xor edx, ebx
	mov ecx, eax
	bswap ecx
	mov DWORD PTR [edi+8], ecx
	mov ecx, edx
	bswap ecx
	mov DWORD PTR [edi+12], ecx
	mov ebx, DWORD PTR [ebp+84]
	mov esi, DWORD PTR [ebp+88]
	mov edi, DWORD PTR [ebp+92]
	mov ebp, DWORD PTR [ebp+96]
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax+400]
	mov ecx, 0
	mov DWORD PTR [eax+400], ecx
	mov DWORD PTR [eax+404], ecx
	lea esp, [esp+660]
	ret
	.p2align 6

vg_cmac_triple_des_absorb:
	lea esp, [esp-716]
	mov eax, DWORD PTR [esp+720]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+724]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+728]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+732]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+736]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+640], ebx
	mov DWORD PTR [eax+644], esi
	mov DWORD PTR [eax+648], edi
	mov DWORD PTR [eax+652], ebp
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 7
	add eax, 1
	jmp 21f
20:
21:
	mov ecx, 8
	sub ecx, eax
	mov edx, DWORD PTR [esp+20]
	cmp edx, ecx
	jb 22f
	jmp 23f
22:
	mov ecx, edx
23:
	mov ebp, ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+4]
	add edi, 408
	add edi, eax
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov esi, 0
	mov edx, DWORD PTR [esp+20]
	sub edx, ebp
	je 27f
	mov esi, 1
	jmp 28f
27:
28:
	mov eax, DWORD PTR [esp+4]
	mov edx, eax
	add edx, 400
	mov ebx, eax
	add ebx, 408
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push eax
	push ecx
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+84], ebx
	mov DWORD PTR [eax+88], esi
	mov DWORD PTR [eax+92], edi
	mov DWORD PTR [eax+96], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+132], eax
	cmp eax, 0
	je 29f
211:
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebp+128]
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+4]
	bswap eax
	bswap edx
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 6
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 15
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 20
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 26
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 29
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 2
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 7
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 11
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 16
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 22
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 25
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 31
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp]
	ror ecx, 1
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 4
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 7
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 13
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 16
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 19
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 30
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 3
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 9
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 12
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 17
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 21
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 23
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 26
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov DWORD PTR [ebp+68], ecx
	mov eax, 3
	mov DWORD PTR [ebp+76], eax
	mov eax, 8
	mov DWORD PTR [ebp+80], eax
212:
	mov eax, 16
	mov DWORD PTR [ebp+72], eax
213:
	mov eax, DWORD PTR [ebp+68]
	ror eax, 25
	and eax, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 27
	and ecx, 258048
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 29
	and ecx, 4032
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 31
	and ecx, 63
	xor eax, ecx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 11
	and ecx, 258048
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 13
	and ecx, 4032
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 15
	and ecx, 63
	xor ebx, ecx
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi]
	shr ecx, 24
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+4]
	and ecx, 65535
	ror ecx, 24
	xor ebx, ecx
	mov ecx, eax
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+4], ecx
	mov ecx, eax
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+8], ecx
	mov ecx, eax
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+16], ecx
	mov ecx, eax
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, ebx
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+28], ecx
	mov ecx, ebx
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, ebx
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+36], ecx
	mov ecx, ebx
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+40], ecx
	mov ecx, ebx
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, ebx
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+48], ecx
	mov eax, DWORD PTR [ebp]
	and eax, 1598085
	xor eax, 282893
	mov ebx, DWORD PTR [ebp]
	and ebx, 3437261
	xor ebx, 1606338
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1340041
	xor ecx, 1060932
	mov ebx, DWORD PTR [ebp]
	and ebx, 3723909
	xor ebx, 2159041
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2388677
	xor edx, 3445699
	mov ebx, DWORD PTR [ebp]
	and ebx, 3699333
	xor ebx, 794639
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1372805
	xor ecx, 2908302
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461961
	xor ebx, 1315720
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 3695491
	xor edi, 524870
	mov ebx, DWORD PTR [ebp]
	and ebx, 3167173
	xor ebx, 3199372
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1601929
	xor ecx, 2400906
	mov ebx, DWORD PTR [ebp]
	and ebx, 3158729
	xor ebx, 3949383
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1864521
	xor edx, 3699465
	mov ebx, DWORD PTR [ebp]
	and ebx, 2642695
	xor ebx, 57536
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1335753
	xor ecx, 1884485
	mov ebx, DWORD PTR [ebp]
	and ebx, 3973961
	xor ebx, 2667019
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp]
	and eax, 3986249
	xor eax, 1085963
	mov ebx, DWORD PTR [ebp]
	and ebx, 840646
	xor ebx, 291086
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3723590
	xor ecx, 2159297
	mov ebx, DWORD PTR [ebp]
	and ebx, 1610499
	xor ebx, 2933640
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2929549
	xor edx, 795020
	mov ebx, DWORD PTR [ebp]
	and ebx, 2413379
	xor ebx, 3674693
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3187587
	xor ecx, 3429191
	mov ebx, DWORD PTR [ebp]
	and ebx, 3183247
	xor ebx, 565698
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 2642511
	xor edi, 3989696
	mov ebx, DWORD PTR [ebp]
	and ebx, 1339590
	xor ebx, 2622403
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1622346
	xor ecx, 1589574
	mov ebx, DWORD PTR [ebp]
	and ebx, 1626957
	xor ebx, 3158157
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1630661
	xor edx, 1343503
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461955
	xor ebx, 2413322
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3186890
	xor ecx, 45705
	mov ebx, DWORD PTR [ebp]
	and ebx, 3715530
	xor ebx, 1859652
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+24]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+20]
	xor ebx, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+56], ebx
	mov eax, DWORD PTR [ebp+28]
	and eax, 3457923
	xor eax, 3469645
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1885068
	xor ebx, 2101262
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1360460
	xor ecx, 2900555
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2642825
	xor ebx, 582085
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2380425
	xor edx, 1089920
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2904966
	xor ebx, 3961609
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3174982
	xor ecx, 1848262
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811974
	xor ebx, 295555
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 824076
	xor edi, 1593860
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2405004
	xor ebx, 1356481
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1323587
	xor ecx, 3154114
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3715654
	xor ebx, 2413452
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2384771
	xor edx, 2671431
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2380745
	xor ebx, 786570
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1630915
	xor ecx, 37128
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3994185
	xor ebx, 3694671
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, 1888454
	xor eax, 2097859
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2924742
	xor ebx, 582025
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3199558
	xor ecx, 3453062
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1335881
	xor ebx, 291392
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807369
	xor edx, 2908234
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3961219
	xor ebx, 3179463
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1594179
	xor ecx, 1102605
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2372492
	xor ebx, 1839118
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 1369033
	xor edi, 3969871
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3727820
	xor ebx, 2376196
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1339593
	xor ecx, 835845
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811980
	xor ebx, 3711179
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807366
	xor edx, 1593996
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1352652
	xor ebx, 1323329
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1622211
	xor ecx, 2630082
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2925379
	xor ebx, 62344
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+52]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+48]
	xor ebx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+60], ebx
	mov edi, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 2
	and ecx, 270336
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 7
	and ecx, 134217729
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 11
	and ecx, 136
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 16
	and ecx, 302120960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 20
	and ecx, 1048576
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 24
	and ecx, 538970112
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 27
	and ecx, 16777248
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 28
	and ecx, 1024
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 3
	and ecx, -2147483648
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 6
	and ecx, 32772
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 10
	and ecx, 4194304
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 11
	and ecx, 528
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 15
	and ecx, 1140850688
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 18
	and ecx, 2
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 23
	and ecx, 69632
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 27
	and ecx, 8912960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 30
	and ecx, 16640
	xor edi, ecx
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edi
	mov eax, DWORD PTR [ebp+80]
	add esi, eax
	mov eax, DWORD PTR [ebp+72]
	sub eax, 1
	mov DWORD PTR [ebp+72], eax
	jne 213b
	mov ecx, DWORD PTR [ebp+80]
	mov eax, 128
	sub eax, ecx
	add esi, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+76]
	sub eax, 1
	mov DWORD PTR [ebp+76], eax
	jne 212b
	sub esi, 504
	mov ecx, DWORD PTR [ebp+64]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 3
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 6
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 8
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 9
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 14
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 15
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 20
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 23
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 26
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 29
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 2
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 7
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 13
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 19
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 25
	and ebx, -2147483136
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 31
	and ebx, 2048
	xor ecx, ebx
	mov DWORD PTR [ebp], ecx
	mov ecx, DWORD PTR [ebp+64]
	ror ecx, 1
	and ecx, 1048576
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 4
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 7
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 13
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 18
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 24
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 25
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 30
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 3
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 6
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 12
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 15
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 17
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 23
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 26
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 29
	and ebx, -2147483136
	xor ecx, ebx
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebp+128]
	mov ebx, DWORD PTR [ebp+132]
	bswap eax
	bswap edx
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add edi, 8
	sub ebx, 1
	mov DWORD PTR [ebp+128], edi
	mov DWORD PTR [ebp+132], ebx
	cmp ebx, 0
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [ebp+84]
	mov esi, DWORD PTR [ebp+88]
	mov edi, DWORD PTR [ebp+92]
	mov ebp, DWORD PTR [ebp+96]
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
	mov ebx, DWORD PTR [esp+4]
	add ebx, 408
	mov edx, DWORD PTR [esp+20]
	sub edx, ebp
	je 214f
	mov ecx, edx
	sub ecx, 1
	mov eax, ecx
	and eax, 7
	sub ecx, eax
	mov ebx, DWORD PTR [esp+16]
	add ebx, ebp
	jmp 215f
214:
215:
	mov esi, ecx
	shr esi, 3
	add ebp, ecx
	mov eax, DWORD PTR [esp+4]
	mov edx, eax
	add edx, 400
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push eax
	push ecx
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+84], ebx
	mov DWORD PTR [eax+88], esi
	mov DWORD PTR [eax+92], edi
	mov DWORD PTR [eax+96], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+132], eax
	cmp eax, 0
	je 216f
218:
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebp+128]
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+4]
	bswap eax
	bswap edx
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 6
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 15
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 20
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 26
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 29
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 2
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 7
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 11
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 16
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 22
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 25
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 31
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp]
	ror ecx, 1
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 4
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 7
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 13
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 16
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 19
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 30
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 3
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 9
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 12
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 17
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 21
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 23
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 26
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov DWORD PTR [ebp+68], ecx
	mov eax, 3
	mov DWORD PTR [ebp+76], eax
	mov eax, 8
	mov DWORD PTR [ebp+80], eax
219:
	mov eax, 16
	mov DWORD PTR [ebp+72], eax
220:
	mov eax, DWORD PTR [ebp+68]
	ror eax, 25
	and eax, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 27
	and ecx, 258048
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 29
	and ecx, 4032
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 31
	and ecx, 63
	xor eax, ecx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 11
	and ecx, 258048
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 13
	and ecx, 4032
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 15
	and ecx, 63
	xor ebx, ecx
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi]
	shr ecx, 24
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+4]
	and ecx, 65535
	ror ecx, 24
	xor ebx, ecx
	mov ecx, eax
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+4], ecx
	mov ecx, eax
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+8], ecx
	mov ecx, eax
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+16], ecx
	mov ecx, eax
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, ebx
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+28], ecx
	mov ecx, ebx
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, ebx
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+36], ecx
	mov ecx, ebx
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+40], ecx
	mov ecx, ebx
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, ebx
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+48], ecx
	mov eax, DWORD PTR [ebp]
	and eax, 1598085
	xor eax, 282893
	mov ebx, DWORD PTR [ebp]
	and ebx, 3437261
	xor ebx, 1606338
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1340041
	xor ecx, 1060932
	mov ebx, DWORD PTR [ebp]
	and ebx, 3723909
	xor ebx, 2159041
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2388677
	xor edx, 3445699
	mov ebx, DWORD PTR [ebp]
	and ebx, 3699333
	xor ebx, 794639
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1372805
	xor ecx, 2908302
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461961
	xor ebx, 1315720
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 3695491
	xor edi, 524870
	mov ebx, DWORD PTR [ebp]
	and ebx, 3167173
	xor ebx, 3199372
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1601929
	xor ecx, 2400906
	mov ebx, DWORD PTR [ebp]
	and ebx, 3158729
	xor ebx, 3949383
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1864521
	xor edx, 3699465
	mov ebx, DWORD PTR [ebp]
	and ebx, 2642695
	xor ebx, 57536
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1335753
	xor ecx, 1884485
	mov ebx, DWORD PTR [ebp]
	and ebx, 3973961
	xor ebx, 2667019
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp]
	and eax, 3986249
	xor eax, 1085963
	mov ebx, DWORD PTR [ebp]
	and ebx, 840646
	xor ebx, 291086
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3723590
	xor ecx, 2159297
	mov ebx, DWORD PTR [ebp]
	and ebx, 1610499
	xor ebx, 2933640
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2929549
	xor edx, 795020
	mov ebx, DWORD PTR [ebp]
	and ebx, 2413379
	xor ebx, 3674693
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3187587
	xor ecx, 3429191
	mov ebx, DWORD PTR [ebp]
	and ebx, 3183247
	xor ebx, 565698
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 2642511
	xor edi, 3989696
	mov ebx, DWORD PTR [ebp]
	and ebx, 1339590
	xor ebx, 2622403
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1622346
	xor ecx, 1589574
	mov ebx, DWORD PTR [ebp]
	and ebx, 1626957
	xor ebx, 3158157
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1630661
	xor edx, 1343503
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461955
	xor ebx, 2413322
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3186890
	xor ecx, 45705
	mov ebx, DWORD PTR [ebp]
	and ebx, 3715530
	xor ebx, 1859652
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+24]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+20]
	xor ebx, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+56], ebx
	mov eax, DWORD PTR [ebp+28]
	and eax, 3457923
	xor eax, 3469645
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1885068
	xor ebx, 2101262
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1360460
	xor ecx, 2900555
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2642825
	xor ebx, 582085
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2380425
	xor edx, 1089920
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2904966
	xor ebx, 3961609
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3174982
	xor ecx, 1848262
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811974
	xor ebx, 295555
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 824076
	xor edi, 1593860
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2405004
	xor ebx, 1356481
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1323587
	xor ecx, 3154114
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3715654
	xor ebx, 2413452
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2384771
	xor edx, 2671431
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2380745
	xor ebx, 786570
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1630915
	xor ecx, 37128
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3994185
	xor ebx, 3694671
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, 1888454
	xor eax, 2097859
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2924742
	xor ebx, 582025
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3199558
	xor ecx, 3453062
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1335881
	xor ebx, 291392
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807369
	xor edx, 2908234
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3961219
	xor ebx, 3179463
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1594179
	xor ecx, 1102605
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2372492
	xor ebx, 1839118
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 1369033
	xor edi, 3969871
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3727820
	xor ebx, 2376196
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1339593
	xor ecx, 835845
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811980
	xor ebx, 3711179
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807366
	xor edx, 1593996
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1352652
	xor ebx, 1323329
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1622211
	xor ecx, 2630082
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2925379
	xor ebx, 62344
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+52]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+48]
	xor ebx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+60], ebx
	mov edi, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 2
	and ecx, 270336
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 7
	and ecx, 134217729
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 11
	and ecx, 136
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 16
	and ecx, 302120960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 20
	and ecx, 1048576
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 24
	and ecx, 538970112
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 27
	and ecx, 16777248
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 28
	and ecx, 1024
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 3
	and ecx, -2147483648
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 6
	and ecx, 32772
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 10
	and ecx, 4194304
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 11
	and ecx, 528
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 15
	and ecx, 1140850688
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 18
	and ecx, 2
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 23
	and ecx, 69632
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 27
	and ecx, 8912960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 30
	and ecx, 16640
	xor edi, ecx
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edi
	mov eax, DWORD PTR [ebp+80]
	add esi, eax
	mov eax, DWORD PTR [ebp+72]
	sub eax, 1
	mov DWORD PTR [ebp+72], eax
	jne 220b
	mov ecx, DWORD PTR [ebp+80]
	mov eax, 128
	sub eax, ecx
	add esi, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+76]
	sub eax, 1
	mov DWORD PTR [ebp+76], eax
	jne 219b
	sub esi, 504
	mov ecx, DWORD PTR [ebp+64]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 3
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 6
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 8
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 9
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 14
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 15
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 20
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 23
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 26
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 29
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 2
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 7
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 13
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 19
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 25
	and ebx, -2147483136
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 31
	and ebx, 2048
	xor ecx, ebx
	mov DWORD PTR [ebp], ecx
	mov ecx, DWORD PTR [ebp+64]
	ror ecx, 1
	and ecx, 1048576
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 4
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 7
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 13
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 18
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 24
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 25
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 30
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 3
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 6
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 12
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 15
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 17
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 23
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 26
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 29
	and ebx, -2147483136
	xor ecx, ebx
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [ebp+128]
	mov ebx, DWORD PTR [ebp+132]
	bswap eax
	bswap edx
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add edi, 8
	sub ebx, 1
	mov DWORD PTR [ebp+128], edi
	mov DWORD PTR [ebp+132], ebx
	cmp ebx, 0
	jne 218b
	jmp 217f
216:
217:
	mov ebx, DWORD PTR [ebp+84]
	mov esi, DWORD PTR [ebp+88]
	mov edi, DWORD PTR [ebp+92]
	mov ebp, DWORD PTR [ebp+96]
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+4]
	add edi, 408
	mov ecx, DWORD PTR [esp+20]
	sub ecx, ebp
	test ecx, ecx
	je 221f
223:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 223b
	jmp 222f
221:
222:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+640]
	mov esi, DWORD PTR [eax+644]
	mov edi, DWORD PTR [eax+648]
	mov ebp, DWORD PTR [eax+652]
	lea esp, [esp+716]
	ret
	.p2align 6

vg_cmac_triple_des_finish:
	lea esp, [esp-712]
	mov eax, DWORD PTR [esp+716]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+720]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+724]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+728]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+640], ebx
	mov DWORD PTR [eax+644], esi
	mov DWORD PTR [eax+648], edi
	mov DWORD PTR [eax+652], ebp
	mov esi, DWORD PTR [esp+4]
	add esi, 400
	mov edi, DWORD PTR [esp+16]
	mov ecx, 8
	test ecx, ecx
	je 20f
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, esi
	je 23f
	sub esi, 1
	and esi, 7
	add esi, 1
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+16]
	mov ebx, eax
	add ebx, 408
	mov edi, DWORD PTR [esp+20]
	push edi
	push esi
	push ebx
	push edx
	push eax
	push ecx
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+84], ebx
	mov DWORD PTR [eax+88], esi
	mov DWORD PTR [eax+92], edi
	mov DWORD PTR [eax+96], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+16]
	cmp eax, 8
	je 25f
	mov eax, 0
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+140], eax
	mov edi, ebp
	add edi, 136
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	cmp edx, 0
	je 27f
29:
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [edi], al
	add ecx, 1
	add edi, 1
	sub edx, 1
	jne 29b
	jmp 28f
27:
28:
	mov eax, 128
	mov BYTE PTR [edi], al
	mov eax, DWORD PTR [ebp+136]
	mov edx, DWORD PTR [ebp+140]
	xor eax, DWORD PTR [esi+392]
	xor edx, DWORD PTR [esi+396]
	jmp 26f
25:
	mov ecx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [esi+384]
	xor edx, DWORD PTR [esi+388]
26:
	mov ecx, DWORD PTR [esp+8]
	xor eax, DWORD PTR [ecx]
	xor edx, DWORD PTR [ecx+4]
	bswap eax
	bswap edx
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 6
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 15
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 20
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 26
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 29
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 2
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 7
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 11
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 16
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 22
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 25
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 31
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp]
	ror ecx, 1
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 4
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 7
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 13
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 16
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 19
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 30
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 3
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 9
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 12
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 17
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 21
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 23
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 26
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov DWORD PTR [ebp+68], ecx
	mov eax, 3
	mov DWORD PTR [ebp+76], eax
	mov eax, 8
	mov DWORD PTR [ebp+80], eax
210:
	mov eax, 16
	mov DWORD PTR [ebp+72], eax
211:
	mov eax, DWORD PTR [ebp+68]
	ror eax, 25
	and eax, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 27
	and ecx, 258048
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 29
	and ecx, 4032
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 31
	and ecx, 63
	xor eax, ecx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 11
	and ecx, 258048
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 13
	and ecx, 4032
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 15
	and ecx, 63
	xor ebx, ecx
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi]
	shr ecx, 24
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+4]
	and ecx, 65535
	ror ecx, 24
	xor ebx, ecx
	mov ecx, eax
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+4], ecx
	mov ecx, eax
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+8], ecx
	mov ecx, eax
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+16], ecx
	mov ecx, eax
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, ebx
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+28], ecx
	mov ecx, ebx
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, ebx
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+36], ecx
	mov ecx, ebx
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+40], ecx
	mov ecx, ebx
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, ebx
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+48], ecx
	mov eax, DWORD PTR [ebp]
	and eax, 1598085
	xor eax, 282893
	mov ebx, DWORD PTR [ebp]
	and ebx, 3437261
	xor ebx, 1606338
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1340041
	xor ecx, 1060932
	mov ebx, DWORD PTR [ebp]
	and ebx, 3723909
	xor ebx, 2159041
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2388677
	xor edx, 3445699
	mov ebx, DWORD PTR [ebp]
	and ebx, 3699333
	xor ebx, 794639
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1372805
	xor ecx, 2908302
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461961
	xor ebx, 1315720
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 3695491
	xor edi, 524870
	mov ebx, DWORD PTR [ebp]
	and ebx, 3167173
	xor ebx, 3199372
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1601929
	xor ecx, 2400906
	mov ebx, DWORD PTR [ebp]
	and ebx, 3158729
	xor ebx, 3949383
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1864521
	xor edx, 3699465
	mov ebx, DWORD PTR [ebp]
	and ebx, 2642695
	xor ebx, 57536
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1335753
	xor ecx, 1884485
	mov ebx, DWORD PTR [ebp]
	and ebx, 3973961
	xor ebx, 2667019
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp]
	and eax, 3986249
	xor eax, 1085963
	mov ebx, DWORD PTR [ebp]
	and ebx, 840646
	xor ebx, 291086
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3723590
	xor ecx, 2159297
	mov ebx, DWORD PTR [ebp]
	and ebx, 1610499
	xor ebx, 2933640
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2929549
	xor edx, 795020
	mov ebx, DWORD PTR [ebp]
	and ebx, 2413379
	xor ebx, 3674693
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3187587
	xor ecx, 3429191
	mov ebx, DWORD PTR [ebp]
	and ebx, 3183247
	xor ebx, 565698
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 2642511
	xor edi, 3989696
	mov ebx, DWORD PTR [ebp]
	and ebx, 1339590
	xor ebx, 2622403
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1622346
	xor ecx, 1589574
	mov ebx, DWORD PTR [ebp]
	and ebx, 1626957
	xor ebx, 3158157
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1630661
	xor edx, 1343503
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461955
	xor ebx, 2413322
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3186890
	xor ecx, 45705
	mov ebx, DWORD PTR [ebp]
	and ebx, 3715530
	xor ebx, 1859652
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+24]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+20]
	xor ebx, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+56], ebx
	mov eax, DWORD PTR [ebp+28]
	and eax, 3457923
	xor eax, 3469645
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1885068
	xor ebx, 2101262
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1360460
	xor ecx, 2900555
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2642825
	xor ebx, 582085
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2380425
	xor edx, 1089920
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2904966
	xor ebx, 3961609
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3174982
	xor ecx, 1848262
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811974
	xor ebx, 295555
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 824076
	xor edi, 1593860
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2405004
	xor ebx, 1356481
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1323587
	xor ecx, 3154114
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3715654
	xor ebx, 2413452
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2384771
	xor edx, 2671431
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2380745
	xor ebx, 786570
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1630915
	xor ecx, 37128
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3994185
	xor ebx, 3694671
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, 1888454
	xor eax, 2097859
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2924742
	xor ebx, 582025
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3199558
	xor ecx, 3453062
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1335881
	xor ebx, 291392
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807369
	xor edx, 2908234
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3961219
	xor ebx, 3179463
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1594179
	xor ecx, 1102605
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2372492
	xor ebx, 1839118
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 1369033
	xor edi, 3969871
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3727820
	xor ebx, 2376196
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1339593
	xor ecx, 835845
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811980
	xor ebx, 3711179
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807366
	xor edx, 1593996
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1352652
	xor ebx, 1323329
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1622211
	xor ecx, 2630082
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2925379
	xor ebx, 62344
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+52]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+48]
	xor ebx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+60], ebx
	mov edi, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 2
	and ecx, 270336
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 7
	and ecx, 134217729
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 11
	and ecx, 136
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 16
	and ecx, 302120960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 20
	and ecx, 1048576
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 24
	and ecx, 538970112
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 27
	and ecx, 16777248
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 28
	and ecx, 1024
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 3
	and ecx, -2147483648
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 6
	and ecx, 32772
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 10
	and ecx, 4194304
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 11
	and ecx, 528
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 15
	and ecx, 1140850688
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 18
	and ecx, 2
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 23
	and ecx, 69632
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 27
	and ecx, 8912960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 30
	and ecx, 16640
	xor edi, ecx
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edi
	mov eax, DWORD PTR [ebp+80]
	add esi, eax
	mov eax, DWORD PTR [ebp+72]
	sub eax, 1
	mov DWORD PTR [ebp+72], eax
	jne 211b
	mov ecx, DWORD PTR [ebp+80]
	mov eax, 128
	sub eax, ecx
	add esi, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+76]
	sub eax, 1
	mov DWORD PTR [ebp+76], eax
	jne 210b
	sub esi, 504
	mov ecx, DWORD PTR [ebp+64]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 3
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 6
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 8
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 9
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 14
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 15
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 20
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 23
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 26
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 29
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 2
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 7
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 13
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 19
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 25
	and ebx, -2147483136
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 31
	and ebx, 2048
	xor ecx, ebx
	mov DWORD PTR [ebp], ecx
	mov ecx, DWORD PTR [ebp+64]
	ror ecx, 1
	and ecx, 1048576
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 4
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 7
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 13
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 18
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 24
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 25
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 30
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 3
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 6
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 12
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 15
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 17
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 23
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 26
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 29
	and ebx, -2147483136
	xor ecx, ebx
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [esp+8]
	bswap eax
	bswap edx
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	mov ebx, DWORD PTR [ebp+84]
	mov esi, DWORD PTR [ebp+88]
	mov edi, DWORD PTR [ebp+92]
	mov ebp, DWORD PTR [ebp+96]
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [eax+640]
	mov esi, DWORD PTR [eax+644]
	mov edi, DWORD PTR [eax+648]
	mov ebp, DWORD PTR [eax+652]
	lea esp, [esp+712]
	ret
	.p2align 6
