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
	cmp edi, esi
	je 20f
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [ebp+3856], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3760], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3764], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3768], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3772], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3776], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3780], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3784], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3788], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3792], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3796], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3800], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3804], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3816]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3820]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3824]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3768], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3828]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3772], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3832]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3776], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3836]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3780], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3840]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3784], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3844]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3788], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3848]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3792], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3852]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3796], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3856]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3800], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3804], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3808], ebx
	mov ebp, edi
	jmp 21f
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3756], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3760], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3764], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3768], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3772], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3776], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3780], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3784], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3788], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3792], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3796], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3800], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3712]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3760]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -393225147
	mul edx
	mov DWORD PTR [edi+3804], eax
	mov edx, -859494029
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3716]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3764]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -320071318
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3720]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3768]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, 1219536762
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3724]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3772]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, 1478102450
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3768], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3728]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -197710369
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3772], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3732]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -949793407
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3776], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3736]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3780], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3740]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3784], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3744]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3788], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3748]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3792], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3752]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3796], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3756]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3800], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3804], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3808], ebx
	mov ebp, edi
21:
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
