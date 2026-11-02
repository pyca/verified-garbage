// The functions of `src/internal/vg_dsa_pow_16_28.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_pow_16_28:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+8], ebx
	mov DWORD PTR [eax+12], esi
	mov DWORD PTR [eax+16], ebp
	mov DWORD PTR [eax+20], edi
	mov edi, eax
	mov ebx, DWORD PTR [edi+64]
	mov ecx, ebx
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov ebp, edi
20:
	mov DWORD PTR [ebp+856], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 20b
	mov eax, 1
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov ebp, edi
21:
	mov DWORD PTR [ebp+1120], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 21b
	mov eax, 1
	mov DWORD PTR [edi+1120], eax
	mov esi, 1040
22:
	mov ecx, 0
	mov ebp, edi
23:
	mov eax, DWORD PTR [ebp+1120]
	mov edx, 0
	cmp edx, ecx
	adc eax, DWORD PTR [ebp+1120]
	mov DWORD PTR [ebp+592], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 23b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+720], eax
	mov ecx, 0
	mov ebp, edi
24:
	mov eax, DWORD PTR [ebp+592]
	mov edx, 0
	cmp edx, ecx
	sbb eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+328], eax
	sbb ecx, ecx
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 24b
	mov eax, DWORD PTR [edi+720]
	mov edx, 0
	cmp edx, ecx
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, eax
	mov ebp, edi
25:
	mov eax, DWORD PTR [ebp+592]
	mov edx, DWORD PTR [ebp+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1120], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 25b
	sub esi, 1
	cmp esi, 0
	jne 22b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1120
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov eax, 0
	mov ebp, edi
26:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 26b
	mov eax, 1
	mov DWORD PTR [edi+1912], eax
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1648
	mov DWORD PTR [esp+24], eax
	mov eax, 1120
	mov DWORD PTR [esp+28], eax
	mov eax, 1912
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1384
	mov DWORD PTR [esp+24], eax
	mov eax, 1384
	mov DWORD PTR [esp+28], eax
	mov eax, 1120
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov esi, 896
27:
	mov ecx, DWORD PTR [edi+2176]
	and ecx, 1
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+4], eax
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1912
	mov DWORD PTR [esp+24], eax
	mov eax, 1648
	mov DWORD PTR [esp+28], eax
	mov eax, 1384
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ecx, DWORD PTR [edi+4]
	mov ebp, edi
28:
	mov eax, DWORD PTR [ebp+1648]
	mov edx, DWORD PTR [ebp+1912]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebp+1648], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 28b
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1384
	mov DWORD PTR [esp+24], eax
	mov eax, 1384
	mov DWORD PTR [esp+28], eax
	mov eax, 1384
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ebp, edi
29:
	mov eax, DWORD PTR [ebp+2180]
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [ebp+2176]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [ebp+2176], edx
	add ebp, 4
	mov edx, edi
	add edx, 108
	cmp ebp, edx
	jne 29b
	mov eax, 0
	and eax, 1
	ror eax, 1
	mov edx, DWORD PTR [edi+2284]
	shr edx, 1
	add edx, eax
	mov DWORD PTR [edi+2284], edx
	sub esi, 1
	cmp esi, 0
	jne 27b
	mov eax, 0
	mov ebp, edi
210:
	mov DWORD PTR [ebp+1912], eax
	add ebp, 4
	mov edx, edi
	add edx, 128
	cmp ebp, edx
	jne 210b
	mov eax, 1
	mov DWORD PTR [edi+1912], eax
	lea esp, [esp-36]
	mov DWORD PTR [esp], edi
	mov eax, 305
	mov DWORD PTR [esp+4], eax
	mov eax, 16
	mov DWORD PTR [esp+8], eax
	mov eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, 328
	mov DWORD PTR [esp+20], eax
	mov eax, 1648
	mov DWORD PTR [esp+24], eax
	mov eax, 1648
	mov DWORD PTR [esp+28], eax
	mov eax, 1912
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	mov ebx, DWORD PTR [edi+8]
	mov esi, DWORD PTR [edi+12]
	mov ebp, DWORD PTR [edi+16]
	mov edi, DWORD PTR [edi+20]
	ret
	.p2align 6
