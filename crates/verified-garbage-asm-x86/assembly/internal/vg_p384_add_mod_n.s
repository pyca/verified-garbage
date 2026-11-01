// The functions of `src/internal/vg_p384_add_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3872], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ecx+40]
	adc eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ecx+44]
	adc eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3756], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3712]
	sub eax, -859494029
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3716]
	sbb eax, -320071318
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3720]
	sbb eax, 1219536762
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3724]
	sbb eax, 1478102450
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3728]
	sbb eax, -197710369
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3732]
	sbb eax, -949793407
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3736]
	sbb eax, -1
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3740]
	sbb eax, -1
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3744]
	sbb eax, -1
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3748]
	sbb eax, -1
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3752]
	sbb eax, -1
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3756]
	sbb eax, -1
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ebp+3760]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3712]
	xor edx, DWORD PTR [ebp+3812]
	and edx, eax
	xor edx, DWORD PTR [ebp+3712]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3716]
	xor edx, DWORD PTR [ebp+3816]
	and edx, eax
	xor edx, DWORD PTR [ebp+3716]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3720]
	xor edx, DWORD PTR [ebp+3820]
	and edx, eax
	xor edx, DWORD PTR [ebp+3720]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3724]
	xor edx, DWORD PTR [ebp+3824]
	and edx, eax
	xor edx, DWORD PTR [ebp+3724]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3728]
	xor edx, DWORD PTR [ebp+3828]
	and edx, eax
	xor edx, DWORD PTR [ebp+3728]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3732]
	xor edx, DWORD PTR [ebp+3832]
	and edx, eax
	xor edx, DWORD PTR [ebp+3732]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3736]
	xor edx, DWORD PTR [ebp+3836]
	and edx, eax
	xor edx, DWORD PTR [ebp+3736]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3740]
	xor edx, DWORD PTR [ebp+3840]
	and edx, eax
	xor edx, DWORD PTR [ebp+3740]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3744]
	xor edx, DWORD PTR [ebp+3844]
	and edx, eax
	xor edx, DWORD PTR [ebp+3744]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3748]
	xor edx, DWORD PTR [ebp+3848]
	and edx, eax
	xor edx, DWORD PTR [ebp+3748]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3752]
	xor edx, DWORD PTR [ebp+3852]
	and edx, eax
	xor edx, DWORD PTR [ebp+3752]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3756]
	xor edx, DWORD PTR [ebp+3856]
	and edx, eax
	xor edx, DWORD PTR [ebp+3756]
	mov DWORD PTR [ecx+44], edx
	mov ebp, DWORD PTR [ebp+3872]
	ret
	.p2align 6
