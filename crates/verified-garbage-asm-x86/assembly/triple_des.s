// The functions of `src/triple_des.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_expand_key:
	lea esp, [esp-532]
	mov eax, DWORD PTR [esp+536]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+540]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+544]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov ebp, eax
	mov edx, DWORD PTR [esp+4]
	mov edi, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	bswap edi
	bswap esi
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 5
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 6
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 7
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 31
	and ecx, 1
	ror ecx, 8
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 9
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 10
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 11
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 31
	and ecx, 1
	ror ecx, 12
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 6
	and ecx, 1
	ror ecx, 13
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 14
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 15
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 30
	and ecx, 1
	ror ecx, 16
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 30
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 29
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 13
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 21
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 29
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 28
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, esi
	shr ecx, 10
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 2
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 18
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, esi
	shr ecx, 3
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, esi
	shr ecx, 19
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 28
	and ecx, 1
	xor eax, ecx
	mov esi, ebx
	mov edi, eax
	mov edx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+20], eax
	add edx, 0
	mov DWORD PTR [ebp+16], edx
20:
	mov eax, DWORD PTR [ebp+20]
	cmp eax, 2
	jb 21f
	cmp eax, 8
	je 23f
	cmp eax, 15
	je 25f
	mov eax, esi
	shr eax, 26
	ror esi, 30
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 26
	ror edi, 30
	xor edi, eax
	and edi, 268435455
	jmp 26f
25:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
26:
	jmp 24f
23:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
24:
	jmp 22f
21:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
22:
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 16
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 24
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 1
	xor eax, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 2
	xor eax, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 3
	xor eax, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 4
	xor eax, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 8
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, edi
	shr ecx, 16
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 8
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, edi
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 24
	and ecx, 1
	xor eax, ecx
	mov edx, DWORD PTR [ebp+16]
	mov ecx, DWORD PTR [ebp+20]
	mov DWORD PTR [edx], eax
	mov DWORD PTR [edx+4], ebx
	add edx, 8
	mov DWORD PTR [ebp+16], edx
	add ecx, 1
	mov DWORD PTR [ebp+20], ecx
	cmp ecx, 16
	jne 20b
	mov edx, DWORD PTR [esp+4]
	mov edi, DWORD PTR [edx+8]
	mov esi, DWORD PTR [edx+12]
	bswap edi
	bswap esi
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 5
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 6
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 7
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 31
	and ecx, 1
	ror ecx, 8
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 9
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 10
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 11
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 31
	and ecx, 1
	ror ecx, 12
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 6
	and ecx, 1
	ror ecx, 13
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 14
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 15
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 30
	and ecx, 1
	ror ecx, 16
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 30
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 29
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 13
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 21
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 29
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 28
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, esi
	shr ecx, 10
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 2
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 18
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, esi
	shr ecx, 3
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, esi
	shr ecx, 19
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 28
	and ecx, 1
	xor eax, ecx
	mov esi, ebx
	mov edi, eax
	mov edx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+20], eax
	add edx, 128
	mov DWORD PTR [ebp+16], edx
27:
	mov eax, DWORD PTR [ebp+20]
	cmp eax, 2
	jb 28f
	cmp eax, 8
	je 210f
	cmp eax, 15
	je 212f
	mov eax, esi
	shr eax, 26
	ror esi, 30
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 26
	ror edi, 30
	xor edi, eax
	and edi, 268435455
	jmp 213f
212:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
213:
	jmp 211f
210:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
211:
	jmp 29f
28:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
29:
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 16
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 24
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 1
	xor eax, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 2
	xor eax, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 3
	xor eax, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 4
	xor eax, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 8
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, edi
	shr ecx, 16
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 8
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, edi
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 24
	and ecx, 1
	xor eax, ecx
	mov edx, DWORD PTR [ebp+16]
	mov ecx, DWORD PTR [ebp+20]
	mov DWORD PTR [edx], eax
	mov DWORD PTR [edx+4], ebx
	add edx, 8
	mov DWORD PTR [ebp+16], edx
	add ecx, 1
	mov DWORD PTR [ebp+20], ecx
	cmp ecx, 16
	jne 27b
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 214f
	mov edx, DWORD PTR [esp+4]
	mov edi, DWORD PTR [edx+16]
	mov esi, DWORD PTR [edx+20]
	bswap edi
	bswap esi
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 5
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 6
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 7
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 31
	and ecx, 1
	ror ecx, 8
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 9
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 10
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 11
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 31
	and ecx, 1
	ror ecx, 12
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 6
	and ecx, 1
	ror ecx, 13
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 14
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 15
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 30
	and ecx, 1
	ror ecx, 16
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 30
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 29
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 13
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 21
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 29
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 28
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, esi
	shr ecx, 10
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 2
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 18
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, esi
	shr ecx, 3
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, esi
	shr ecx, 19
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 28
	and ecx, 1
	xor eax, ecx
	mov esi, ebx
	mov edi, eax
	mov edx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+20], eax
	add edx, 256
	mov DWORD PTR [ebp+16], edx
216:
	mov eax, DWORD PTR [ebp+20]
	cmp eax, 2
	jb 217f
	cmp eax, 8
	je 219f
	cmp eax, 15
	je 221f
	mov eax, esi
	shr eax, 26
	ror esi, 30
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 26
	ror edi, 30
	xor edi, eax
	and edi, 268435455
	jmp 222f
221:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
222:
	jmp 220f
219:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
220:
	jmp 218f
217:
	mov eax, esi
	shr eax, 27
	ror esi, 31
	xor esi, eax
	and esi, 268435455
	mov eax, edi
	shr eax, 27
	ror edi, 31
	xor edi, eax
	and edi, 268435455
218:
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 16
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 24
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 1
	xor eax, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 2
	xor eax, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 3
	xor eax, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 4
	xor eax, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 8
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, edi
	shr ecx, 16
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, edi
	shr ecx, 8
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, edi
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 24
	and ecx, 1
	xor eax, ecx
	mov edx, DWORD PTR [ebp+16]
	mov ecx, DWORD PTR [ebp+20]
	mov DWORD PTR [edx], eax
	mov DWORD PTR [edx+4], ebx
	add edx, 8
	mov DWORD PTR [ebp+16], edx
	add ecx, 1
	mov DWORD PTR [ebp+20], ecx
	cmp ecx, 16
	jne 216b
	jmp 215f
214:
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edx+256], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edx+260], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edx+264], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edx+268], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edx+272], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edx+276], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edx+280], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edx+284], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edx+288], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edx+292], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edx+296], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edx+300], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edx+304], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edx+308], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edx+312], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edx+316], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edx+320], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edx+324], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edx+328], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edx+332], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edx+336], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edx+340], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edx+344], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edx+348], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edx+352], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edx+356], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edx+360], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edx+364], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edx+368], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edx+372], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edx+376], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edx+380], eax
215:
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	lea esp, [esp+532]
	ret
	.p2align 6

vg_triple_des_ecb_encrypt:
	lea esp, [esp-1044]
	mov eax, DWORD PTR [esp+1048]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1052]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1056]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+512], ebp
	mov DWORD PTR [eax+516], ebx
	mov DWORD PTR [eax+520], esi
	mov DWORD PTR [eax+524], edi
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+12]
	cmp edi, 0
	je 20f
22:
	push ebp
	push esi
	push ebx
	call {vg_triple_des_encrypt_block}
	pop eax
	pop eax
	pop eax
	add esi, 8
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+512]
	mov ebx, DWORD PTR [eax+516]
	mov esi, DWORD PTR [eax+520]
	mov edi, DWORD PTR [eax+524]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	lea esp, [esp+1044]
	ret
	.p2align 6

vg_triple_des_ecb_decrypt:
	lea esp, [esp-1044]
	mov eax, DWORD PTR [esp+1048]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1052]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1056]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+512], ebp
	mov DWORD PTR [eax+516], ebx
	mov DWORD PTR [eax+520], esi
	mov DWORD PTR [eax+524], edi
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+12]
	cmp edi, 0
	je 20f
22:
	push ebp
	push esi
	push ebx
	call {vg_triple_des_decrypt_block}
	pop eax
	pop eax
	pop eax
	add esi, 8
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+512]
	mov ebx, DWORD PTR [eax+516]
	mov esi, DWORD PTR [eax+520]
	mov edi, DWORD PTR [eax+524]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	lea esp, [esp+1044]
	ret
	.p2align 6
