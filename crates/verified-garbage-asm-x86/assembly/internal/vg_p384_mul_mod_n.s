// The functions of `src/internal/vg_p384_mul_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3860], ebx
	mov DWORD PTR [eax+3864], esi
	mov DWORD PTR [eax+3868], edi
	mov DWORD PTR [eax+3872], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3712], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3760], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3712]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3712]
	adc edx, 0
	mov DWORD PTR [ebp+3712], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3760]
	add eax, ebx
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3764]
	adc eax, 0
	mov DWORD PTR [ebp+3764], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3764]
	add eax, ebx
	mov DWORD PTR [ebp+3764], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3716]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3764]
	add eax, ebx
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3768]
	adc eax, 0
	mov DWORD PTR [ebp+3768], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3768]
	add eax, ebx
	mov DWORD PTR [ebp+3768], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3720]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3768]
	add eax, ebx
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3772]
	adc eax, 0
	mov DWORD PTR [ebp+3772], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3772]
	add eax, ebx
	mov DWORD PTR [ebp+3772], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3724]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3772]
	add eax, ebx
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3776]
	adc eax, 0
	mov DWORD PTR [ebp+3776], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3776]
	add eax, ebx
	mov DWORD PTR [ebp+3776], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [ebp+3728]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3776]
	add eax, ebx
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3780]
	adc eax, 0
	mov DWORD PTR [ebp+3780], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3780]
	add eax, ebx
	mov DWORD PTR [ebp+3780], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [ebp+3732]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3780]
	add eax, ebx
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [ebp+3784]
	adc eax, 0
	mov DWORD PTR [ebp+3784], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3784]
	add eax, ebx
	mov DWORD PTR [ebp+3784], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [ebp+3736]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3784]
	add eax, ebx
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [ebp+3788]
	adc eax, 0
	mov DWORD PTR [ebp+3788], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3788]
	add eax, ebx
	mov DWORD PTR [ebp+3788], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [ebp+3740]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3788]
	add eax, ebx
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [ebp+3792]
	adc eax, 0
	mov DWORD PTR [ebp+3792], eax
	mov ecx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3792]
	add eax, ebx
	mov DWORD PTR [ebp+3792], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [ebp+3744]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3792]
	add eax, ebx
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [ebp+3796]
	adc eax, 0
	mov DWORD PTR [ebp+3796], eax
	mov ecx, DWORD PTR [edi+36]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3796]
	add eax, ebx
	mov DWORD PTR [ebp+3796], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [ebp+3748]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3796]
	add eax, ebx
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [ebp+3800]
	adc eax, 0
	mov DWORD PTR [ebp+3800], eax
	mov ecx, DWORD PTR [edi+40]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3800]
	add eax, ebx
	mov DWORD PTR [ebp+3800], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [ebp+3752]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3800]
	add eax, ebx
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [ebp+3804]
	adc eax, 0
	mov DWORD PTR [ebp+3804], eax
	mov ecx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3804]
	add eax, ebx
	mov DWORD PTR [ebp+3804], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [ebp+3756]
	mov ecx, -393225147
	mul ecx
	mov ecx, eax
	mov eax, -859494029
	mul ecx
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -320071318
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 1219536762
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 1478102450
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -197710369
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -949793407
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3804]
	add eax, ebx
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [ebp+3808]
	adc eax, 0
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [ebp+3760]
	sub eax, -859494029
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3764]
	sbb eax, -320071318
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3768]
	sbb eax, 1219536762
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3772]
	sbb eax, 1478102450
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3776]
	sbb eax, -197710369
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3780]
	sbb eax, -949793407
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3784]
	sbb eax, -1
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3788]
	sbb eax, -1
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3792]
	sbb eax, -1
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3796]
	sbb eax, -1
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3800]
	sbb eax, -1
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3804]
	sbb eax, -1
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ebp+3808]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3864]
	mov edi, DWORD PTR [ebp+3868]
	mov edx, DWORD PTR [ebp+3760]
	xor edx, DWORD PTR [ebp+3812]
	and edx, eax
	xor edx, DWORD PTR [ebp+3760]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3764]
	xor edx, DWORD PTR [ebp+3816]
	and edx, eax
	xor edx, DWORD PTR [ebp+3764]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3768]
	xor edx, DWORD PTR [ebp+3820]
	and edx, eax
	xor edx, DWORD PTR [ebp+3768]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3772]
	xor edx, DWORD PTR [ebp+3824]
	and edx, eax
	xor edx, DWORD PTR [ebp+3772]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3776]
	xor edx, DWORD PTR [ebp+3828]
	and edx, eax
	xor edx, DWORD PTR [ebp+3776]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3780]
	xor edx, DWORD PTR [ebp+3832]
	and edx, eax
	xor edx, DWORD PTR [ebp+3780]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3784]
	xor edx, DWORD PTR [ebp+3836]
	and edx, eax
	xor edx, DWORD PTR [ebp+3784]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3788]
	xor edx, DWORD PTR [ebp+3840]
	and edx, eax
	xor edx, DWORD PTR [ebp+3788]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3792]
	xor edx, DWORD PTR [ebp+3844]
	and edx, eax
	xor edx, DWORD PTR [ebp+3792]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3796]
	xor edx, DWORD PTR [ebp+3848]
	and edx, eax
	xor edx, DWORD PTR [ebp+3796]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3800]
	xor edx, DWORD PTR [ebp+3852]
	and edx, eax
	xor edx, DWORD PTR [ebp+3800]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3804]
	xor edx, DWORD PTR [ebp+3856]
	and edx, eax
	xor edx, DWORD PTR [ebp+3804]
	mov DWORD PTR [ecx+44], edx
	mov ebx, DWORD PTR [ebp+3860]
	mov ebp, DWORD PTR [ebp+3872]
	ret
	.p2align 6
