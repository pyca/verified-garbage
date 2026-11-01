// The functions of `src/brainpoolp384r1_mont.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_mul_mod_p:
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3712]
	adc edx, 0
	mov DWORD PTR [ebp+3712], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, -358692827
	mul ecx
	mov ecx, eax
	mov eax, 822602835
	mul ecx
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -2025390061
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1877140879
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1395415255
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 2142703907
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 313645593
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -313239884
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -1934025086
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
	sub eax, 822602835
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3764]
	sbb eax, -2025390061
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3768]
	sbb eax, -1877140879
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3772]
	sbb eax, -1395415255
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3776]
	sbb eax, 2142703907
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3780]
	sbb eax, 313645593
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3784]
	sbb eax, -313239884
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3788]
	sbb eax, 355430665
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3792]
	sbb eax, 1357267423
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3796]
	sbb eax, 257781630
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3800]
	sbb eax, -1556583128
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3804]
	sbb eax, -1934025086
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

vg_brainpoolp384r1_add_mod_p:
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
	sub eax, 822602835
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3716]
	sbb eax, -2025390061
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3720]
	sbb eax, -1877140879
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3724]
	sbb eax, -1395415255
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3728]
	sbb eax, 2142703907
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3732]
	sbb eax, 313645593
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3736]
	sbb eax, -313239884
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3740]
	sbb eax, 355430665
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3744]
	sbb eax, 1357267423
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3748]
	sbb eax, 257781630
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3752]
	sbb eax, -1556583128
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3756]
	sbb eax, -1934025086
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

vg_brainpoolp384r1_sub_mod_p:
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
	mov edx, 822602835
	and edx, eax
	mov DWORD PTR [ebp+3812], edx
	mov edx, -2025390061
	and edx, eax
	mov DWORD PTR [ebp+3816], edx
	mov edx, -1877140879
	and edx, eax
	mov DWORD PTR [ebp+3820], edx
	mov edx, -1395415255
	and edx, eax
	mov DWORD PTR [ebp+3824], edx
	mov edx, 2142703907
	and edx, eax
	mov DWORD PTR [ebp+3828], edx
	mov edx, 313645593
	and edx, eax
	mov DWORD PTR [ebp+3832], edx
	mov edx, -313239884
	and edx, eax
	mov DWORD PTR [ebp+3836], edx
	mov edx, 355430665
	and edx, eax
	mov DWORD PTR [ebp+3840], edx
	mov edx, 1357267423
	and edx, eax
	mov DWORD PTR [ebp+3844], edx
	mov edx, 257781630
	and edx, eax
	mov DWORD PTR [ebp+3848], edx
	mov edx, -1556583128
	and edx, eax
	mov DWORD PTR [ebp+3852], edx
	mov edx, -1934025086
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

vg_brainpoolp384r1_mul_mod_n:
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3712]
	adc edx, 0
	mov DWORD PTR [ebp+3712], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3716]
	adc edx, 0
	mov DWORD PTR [ebp+3716], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3720]
	adc edx, 0
	mov DWORD PTR [ebp+3720], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3724]
	adc edx, 0
	mov DWORD PTR [ebp+3724], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3728]
	adc edx, 0
	mov DWORD PTR [ebp+3728], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3732]
	adc edx, 0
	mov DWORD PTR [ebp+3732], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3736]
	adc edx, 0
	mov DWORD PTR [ebp+3736], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3740]
	adc edx, 0
	mov DWORD PTR [ebp+3740], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3744]
	adc edx, 0
	mov DWORD PTR [ebp+3744], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3748]
	adc edx, 0
	mov DWORD PTR [ebp+3748], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3752]
	adc edx, 0
	mov DWORD PTR [ebp+3752], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1934025086
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
	mov ecx, 1555413907
	mul ecx
	mov ecx, eax
	mov eax, -385587867
	mul ecx
	add eax, DWORD PTR [ebp+3756]
	adc edx, 0
	mov DWORD PTR [ebp+3756], eax
	mov ebx, edx
	mov eax, 998781442
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3760]
	adc edx, 0
	mov DWORD PTR [ebp+3760], eax
	mov ebx, edx
	mov eax, 1803535120
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3764]
	adc edx, 0
	mov DWORD PTR [ebp+3764], eax
	mov ebx, edx
	mov eax, -818235729
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3768]
	adc edx, 0
	mov DWORD PTR [ebp+3768], eax
	mov ebx, edx
	mov eax, -1409014361
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3772]
	adc edx, 0
	mov DWORD PTR [ebp+3772], eax
	mov ebx, edx
	mov eax, 521563756
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -313239885
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, 355430665
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, 1357267423
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, 257781630
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1556583128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -1934025086
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
	sub eax, -385587867
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3764]
	sbb eax, 998781442
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3768]
	sbb eax, 1803535120
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3772]
	sbb eax, -818235729
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3776]
	sbb eax, -1409014361
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3780]
	sbb eax, 521563756
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3784]
	sbb eax, -313239885
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3788]
	sbb eax, 355430665
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3792]
	sbb eax, 1357267423
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3796]
	sbb eax, 257781630
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3800]
	sbb eax, -1556583128
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3804]
	sbb eax, -1934025086
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

vg_brainpoolp384r1_add_mod_n:
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
	sub eax, -385587867
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [ebp+3716]
	sbb eax, 998781442
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3720]
	sbb eax, 1803535120
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3724]
	sbb eax, -818235729
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3728]
	sbb eax, -1409014361
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3732]
	sbb eax, 521563756
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3736]
	sbb eax, -313239885
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3740]
	sbb eax, 355430665
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3744]
	sbb eax, 1357267423
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3748]
	sbb eax, 257781630
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3752]
	sbb eax, -1556583128
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3756]
	sbb eax, -1934025086
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

vg_brainpoolp384r1_sub_mod_n:
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
	mov edx, -385587867
	and edx, eax
	mov DWORD PTR [ebp+3812], edx
	mov edx, 998781442
	and edx, eax
	mov DWORD PTR [ebp+3816], edx
	mov edx, 1803535120
	and edx, eax
	mov DWORD PTR [ebp+3820], edx
	mov edx, -818235729
	and edx, eax
	mov DWORD PTR [ebp+3824], edx
	mov edx, -1409014361
	and edx, eax
	mov DWORD PTR [ebp+3828], edx
	mov edx, 521563756
	and edx, eax
	mov DWORD PTR [ebp+3832], edx
	mov edx, -313239885
	and edx, eax
	mov DWORD PTR [ebp+3836], edx
	mov edx, 355430665
	and edx, eax
	mov DWORD PTR [ebp+3840], edx
	mov edx, 1357267423
	and edx, eax
	mov DWORD PTR [ebp+3844], edx
	mov edx, 257781630
	and edx, eax
	mov DWORD PTR [ebp+3848], edx
	mov edx, -1556583128
	and edx, eax
	mov DWORD PTR [ebp+3852], edx
	mov edx, -1934025086
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
