// The functions of `src/internal/vg_p384_sub_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_sub_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3872], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ecx+32]
	sbb eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ecx+36]
	sbb eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ecx+40]
	sbb eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ecx+44]
	sbb eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3756], eax
	sbb eax, eax
	mov edx, -859494029
	and edx, eax
	mov DWORD PTR [ebp+3812], edx
	mov edx, -320071318
	and edx, eax
	mov DWORD PTR [ebp+3816], edx
	mov edx, 1219536762
	and edx, eax
	mov DWORD PTR [ebp+3820], edx
	mov edx, 1478102450
	and edx, eax
	mov DWORD PTR [ebp+3824], edx
	mov edx, -197710369
	and edx, eax
	mov DWORD PTR [ebp+3828], edx
	mov edx, -949793407
	and edx, eax
	mov DWORD PTR [ebp+3832], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3836], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3840], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3844], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3848], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3852], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3856], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3712]
	add edx, DWORD PTR [ebp+3812]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3716]
	adc edx, DWORD PTR [ebp+3816]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3720]
	adc edx, DWORD PTR [ebp+3820]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3724]
	adc edx, DWORD PTR [ebp+3824]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3728]
	adc edx, DWORD PTR [ebp+3828]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3732]
	adc edx, DWORD PTR [ebp+3832]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3736]
	adc edx, DWORD PTR [ebp+3836]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3740]
	adc edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3744]
	adc edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3748]
	adc edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3752]
	adc edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3756]
	adc edx, DWORD PTR [ebp+3856]
	mov DWORD PTR [ecx+44], edx
	mov ebp, DWORD PTR [ebp+3872]
	ret
	.p2align 6
