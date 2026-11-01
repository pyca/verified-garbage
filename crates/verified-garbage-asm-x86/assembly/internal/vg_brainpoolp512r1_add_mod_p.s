// The functions of `src/internal/vg_brainpoolp512r1_add_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_add_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ecx+40]
	adc eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ecx+44]
	adc eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ecx+48]
	adc eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ecx+52]
	adc eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ecx+56]
	adc eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ecx+60]
	adc eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3644], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3584]
	sub eax, 1480214771
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3588]
	sbb eax, 682254422
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3592]
	sbb eax, 763545221
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3596]
	sbb eax, 679608111
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3600]
	sbb eax, -425492250
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3604]
	sbb eax, -1362255574
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3608]
	sbb eax, -1681495998
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ebp+3612]
	sbb eax, 2102237952
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ebp+3616]
	sbb eax, 1882392689
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ebp+3620]
	sbb eax, -698114870
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ebp+3624]
	sbb eax, -1278619122
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [ebp+3628]
	sbb eax, -886010445
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3632]
	sbb eax, 868875271
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3636]
	sbb eax, 1070917294
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3640]
	sbb eax, -605436789
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3644]
	sbb eax, -1428316744
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3648]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3584]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3584]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3588]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3588]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3592]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3592]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3596]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3596]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3600]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3600]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3604]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3604]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3608]
	xor edx, DWORD PTR [ebp+3740]
	and edx, eax
	xor edx, DWORD PTR [ebp+3608]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3612]
	xor edx, DWORD PTR [ebp+3744]
	and edx, eax
	xor edx, DWORD PTR [ebp+3612]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3616]
	xor edx, DWORD PTR [ebp+3748]
	and edx, eax
	xor edx, DWORD PTR [ebp+3616]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3620]
	xor edx, DWORD PTR [ebp+3752]
	and edx, eax
	xor edx, DWORD PTR [ebp+3620]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3624]
	xor edx, DWORD PTR [ebp+3756]
	and edx, eax
	xor edx, DWORD PTR [ebp+3624]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3628]
	xor edx, DWORD PTR [ebp+3760]
	and edx, eax
	xor edx, DWORD PTR [ebp+3628]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3632]
	xor edx, DWORD PTR [ebp+3764]
	and edx, eax
	xor edx, DWORD PTR [ebp+3632]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3636]
	xor edx, DWORD PTR [ebp+3768]
	and edx, eax
	xor edx, DWORD PTR [ebp+3636]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3640]
	xor edx, DWORD PTR [ebp+3772]
	and edx, eax
	xor edx, DWORD PTR [ebp+3640]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3644]
	xor edx, DWORD PTR [ebp+3776]
	and edx, eax
	xor edx, DWORD PTR [ebp+3644]
	mov DWORD PTR [ecx+60], edx
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6
