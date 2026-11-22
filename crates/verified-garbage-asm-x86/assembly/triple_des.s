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
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	lea esp, [esp+532]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
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
	mov ecx, edi
	cmp edi, 32
	jb 23f
	mov ecx, 32
	jmp 24f
23:
24:
	mov edx, ebp
	add edx, 528
25:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edx+4], eax
	add esi, 8
	add edx, 8
	sub ecx, 1
	jne 25b
	mov ecx, edi
	cmp edi, 32
	jb 26f
	mov ecx, 32
	jmp 27f
26:
27:
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub esi, ecx
	push ebx
	push ebp
	call {vg_triple_des_encrypt_batch}
	pop eax
	pop eax
	mov ecx, edi
	cmp edi, 32
	jb 28f
	mov ecx, 32
	jmp 29f
28:
29:
	mov edx, ebp
	add edx, 528
210:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [esi+4], eax
	add edx, 8
	add esi, 8
	sub ecx, 1
	jne 210b
	mov ecx, edi
	cmp edi, 32
	jb 211f
	mov ecx, 32
	jmp 212f
211:
212:
	sub edi, ecx
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+512]
	mov ebx, DWORD PTR [eax+516]
	mov esi, DWORD PTR [eax+520]
	mov edi, DWORD PTR [eax+524]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	lea esp, [esp+1044]
	lea esp, [esp-1060]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	lea esp, [esp+1060]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
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
	mov ecx, edi
	cmp edi, 32
	jb 23f
	mov ecx, 32
	jmp 24f
23:
24:
	mov edx, ebp
	add edx, 528
25:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edx+4], eax
	add esi, 8
	add edx, 8
	sub ecx, 1
	jne 25b
	mov ecx, edi
	cmp edi, 32
	jb 26f
	mov ecx, 32
	jmp 27f
26:
27:
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	sub esi, ecx
	push ebx
	push ebp
	call {vg_triple_des_decrypt_batch}
	pop eax
	pop eax
	mov ecx, edi
	cmp edi, 32
	jb 28f
	mov ecx, 32
	jmp 29f
28:
29:
	mov edx, ebp
	add edx, 528
210:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [esi+4], eax
	add edx, 8
	add esi, 8
	sub ecx, 1
	jne 210b
	mov ecx, edi
	cmp edi, 32
	jb 211f
	mov ecx, 32
	jmp 212f
211:
212:
	sub edi, ecx
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+512]
	mov ebx, DWORD PTR [eax+516]
	mov esi, DWORD PTR [eax+520]
	mov edi, DWORD PTR [eax+524]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	lea esp, [esp+1044]
	lea esp, [esp-1060]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	lea esp, [esp+1060]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
