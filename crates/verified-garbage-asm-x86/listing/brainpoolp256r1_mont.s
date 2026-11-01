// The functions of `src/brainpoolp256r1_mont.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_mul_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3940], ebx
	mov DWORD PTR [eax+3944], esi
	mov DWORD PTR [eax+3948], edi
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3872], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3840]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3872]
	add eax, ebx
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3876]
	adc eax, 0
	mov DWORD PTR [ebp+3876], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3876]
	add eax, ebx
	mov DWORD PTR [ebp+3876], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3844]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3876]
	add eax, ebx
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3880]
	adc eax, 0
	mov DWORD PTR [ebp+3880], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3880]
	add eax, ebx
	mov DWORD PTR [ebp+3880], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3848]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3880]
	add eax, ebx
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3884]
	adc eax, 0
	mov DWORD PTR [ebp+3884], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3884]
	add eax, ebx
	mov DWORD PTR [ebp+3884], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3852]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3884]
	add eax, ebx
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3888]
	adc eax, 0
	mov DWORD PTR [ebp+3888], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3888]
	add eax, ebx
	mov DWORD PTR [ebp+3888], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3856]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3888]
	add eax, ebx
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3892]
	adc eax, 0
	mov DWORD PTR [ebp+3892], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3892]
	add eax, ebx
	mov DWORD PTR [ebp+3892], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3860]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3892]
	add eax, ebx
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3896]
	adc eax, 0
	mov DWORD PTR [ebp+3896], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3896]
	add eax, ebx
	mov DWORD PTR [ebp+3896], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3900], eax
	mov eax, DWORD PTR [ebp+3864]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3896]
	add eax, ebx
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3900]
	adc eax, 0
	mov DWORD PTR [ebp+3900], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3896]
	adc edx, 0
	mov DWORD PTR [ebp+3896], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3900]
	add eax, ebx
	mov DWORD PTR [ebp+3900], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ebp+3868]
	mov ecx, -822244935
	mul ecx
	mov ecx, eax
	mov eax, 527324023
	mul ecx
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, 538134557
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -718921688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, 1849423395
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1652322958
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3896]
	adc edx, 0
	mov DWORD PTR [ebp+3896], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3900]
	add eax, ebx
	mov DWORD PTR [ebp+3900], eax
	mov eax, DWORD PTR [ebp+3904]
	adc eax, 0
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ebp+3872]
	sub eax, 527324023
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ebp+3876]
	sbb eax, 538134557
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ebp+3880]
	sbb eax, -718921688
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ebp+3884]
	sbb eax, 1849423395
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ebp+3888]
	sbb eax, -1652322958
	mov DWORD PTR [ebp+3924], eax
	mov eax, DWORD PTR [ebp+3892]
	sbb eax, 1046874768
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3896]
	sbb eax, -1578194500
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3900]
	sbb eax, -1443145765
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3904]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3944]
	mov edi, DWORD PTR [ebp+3948]
	mov edx, DWORD PTR [ebp+3872]
	xor edx, DWORD PTR [ebp+3908]
	and edx, eax
	xor edx, DWORD PTR [ebp+3872]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3876]
	xor edx, DWORD PTR [ebp+3912]
	and edx, eax
	xor edx, DWORD PTR [ebp+3876]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3880]
	xor edx, DWORD PTR [ebp+3916]
	and edx, eax
	xor edx, DWORD PTR [ebp+3880]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3884]
	xor edx, DWORD PTR [ebp+3920]
	and edx, eax
	xor edx, DWORD PTR [ebp+3884]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3888]
	xor edx, DWORD PTR [ebp+3924]
	and edx, eax
	xor edx, DWORD PTR [ebp+3888]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3892]
	xor edx, DWORD PTR [ebp+3928]
	and edx, eax
	xor edx, DWORD PTR [ebp+3892]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3896]
	xor edx, DWORD PTR [ebp+3932]
	and edx, eax
	xor edx, DWORD PTR [ebp+3896]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3900]
	xor edx, DWORD PTR [ebp+3936]
	and edx, eax
	xor edx, DWORD PTR [ebp+3900]
	mov DWORD PTR [ecx+28], edx
	mov ebx, DWORD PTR [ebp+3940]
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6

vg_brainpoolp256r1_add_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3840]
	sub eax, 527324023
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, 538134557
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, -718921688
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, 1849423395
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, -1652322958
	mov DWORD PTR [ebp+3924], eax
	mov eax, DWORD PTR [ebp+3860]
	sbb eax, 1046874768
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3864]
	sbb eax, -1578194500
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3868]
	sbb eax, -1443145765
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3872]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3840]
	xor edx, DWORD PTR [ebp+3908]
	and edx, eax
	xor edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	xor edx, DWORD PTR [ebp+3912]
	and edx, eax
	xor edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	xor edx, DWORD PTR [ebp+3916]
	and edx, eax
	xor edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	xor edx, DWORD PTR [ebp+3920]
	and edx, eax
	xor edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	xor edx, DWORD PTR [ebp+3924]
	and edx, eax
	xor edx, DWORD PTR [ebp+3856]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	xor edx, DWORD PTR [ebp+3928]
	and edx, eax
	xor edx, DWORD PTR [ebp+3860]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	xor edx, DWORD PTR [ebp+3932]
	and edx, eax
	xor edx, DWORD PTR [ebp+3864]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	xor edx, DWORD PTR [ebp+3936]
	and edx, eax
	xor edx, DWORD PTR [ebp+3868]
	mov DWORD PTR [ecx+28], edx
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6

vg_brainpoolp256r1_sub_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	sbb eax, eax
	mov edx, 527324023
	and edx, eax
	mov DWORD PTR [ebp+3908], edx
	mov edx, 538134557
	and edx, eax
	mov DWORD PTR [ebp+3912], edx
	mov edx, -718921688
	and edx, eax
	mov DWORD PTR [ebp+3916], edx
	mov edx, 1849423395
	and edx, eax
	mov DWORD PTR [ebp+3920], edx
	mov edx, -1652322958
	and edx, eax
	mov DWORD PTR [ebp+3924], edx
	mov edx, 1046874768
	and edx, eax
	mov DWORD PTR [ebp+3928], edx
	mov edx, -1578194500
	and edx, eax
	mov DWORD PTR [ebp+3932], edx
	mov edx, -1443145765
	and edx, eax
	mov DWORD PTR [ebp+3936], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3840]
	add edx, DWORD PTR [ebp+3908]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	adc edx, DWORD PTR [ebp+3912]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	adc edx, DWORD PTR [ebp+3916]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	adc edx, DWORD PTR [ebp+3920]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	adc edx, DWORD PTR [ebp+3924]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	adc edx, DWORD PTR [ebp+3928]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	adc edx, DWORD PTR [ebp+3932]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	adc edx, DWORD PTR [ebp+3936]
	mov DWORD PTR [ecx+28], edx
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6

vg_brainpoolp256r1_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3940], ebx
	mov DWORD PTR [eax+3944], esi
	mov DWORD PTR [eax+3948], edi
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3872], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3840]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3872]
	add eax, ebx
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3876]
	adc eax, 0
	mov DWORD PTR [ebp+3876], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3876]
	add eax, ebx
	mov DWORD PTR [ebp+3876], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3844]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3876]
	add eax, ebx
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3880]
	adc eax, 0
	mov DWORD PTR [ebp+3880], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3880]
	add eax, ebx
	mov DWORD PTR [ebp+3880], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3848]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3880]
	add eax, ebx
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3884]
	adc eax, 0
	mov DWORD PTR [ebp+3884], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3884]
	add eax, ebx
	mov DWORD PTR [ebp+3884], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3852]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ebp+3852], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3884]
	add eax, ebx
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3888]
	adc eax, 0
	mov DWORD PTR [ebp+3888], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3888]
	add eax, ebx
	mov DWORD PTR [ebp+3888], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3856]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ebp+3856], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3888]
	add eax, ebx
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3892]
	adc eax, 0
	mov DWORD PTR [ebp+3892], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3892]
	add eax, ebx
	mov DWORD PTR [ebp+3892], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3860]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ebp+3860], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3892]
	add eax, ebx
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3896]
	adc eax, 0
	mov DWORD PTR [ebp+3896], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3896]
	add eax, ebx
	mov DWORD PTR [ebp+3896], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3900], eax
	mov eax, DWORD PTR [ebp+3864]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3864]
	adc edx, 0
	mov DWORD PTR [ebp+3864], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3896]
	add eax, ebx
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3900]
	adc eax, 0
	mov DWORD PTR [ebp+3900], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3896]
	adc edx, 0
	mov DWORD PTR [ebp+3896], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3900]
	add eax, ebx
	mov DWORD PTR [ebp+3900], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ebp+3868]
	mov ecx, -877392151
	mul ecx
	mov ecx, eax
	mov eax, -1756866905
	mul ecx
	add eax, DWORD PTR [ebp+3868]
	adc edx, 0
	mov DWORD PTR [ebp+3868], eax
	mov ebx, edx
	mov eax, -1877078398
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3872]
	adc edx, 0
	mov DWORD PTR [ebp+3872], eax
	mov ebx, edx
	mov eax, -1251891465
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3876]
	adc edx, 0
	mov DWORD PTR [ebp+3876], eax
	mov ebx, edx
	mov eax, -1942390109
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3880]
	adc edx, 0
	mov DWORD PTR [ebp+3880], eax
	mov ebx, edx
	mov eax, -1652322959
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3884]
	adc edx, 0
	mov DWORD PTR [ebp+3884], eax
	mov ebx, edx
	mov eax, 1046874768
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3888]
	adc edx, 0
	mov DWORD PTR [ebp+3888], eax
	mov ebx, edx
	mov eax, -1578194500
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3892]
	adc edx, 0
	mov DWORD PTR [ebp+3892], eax
	mov ebx, edx
	mov eax, -1443145765
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3896]
	adc edx, 0
	mov DWORD PTR [ebp+3896], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3900]
	add eax, ebx
	mov DWORD PTR [ebp+3900], eax
	mov eax, DWORD PTR [ebp+3904]
	adc eax, 0
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ebp+3872]
	sub eax, -1756866905
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ebp+3876]
	sbb eax, -1877078398
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ebp+3880]
	sbb eax, -1251891465
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ebp+3884]
	sbb eax, -1942390109
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ebp+3888]
	sbb eax, -1652322959
	mov DWORD PTR [ebp+3924], eax
	mov eax, DWORD PTR [ebp+3892]
	sbb eax, 1046874768
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3896]
	sbb eax, -1578194500
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3900]
	sbb eax, -1443145765
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3904]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3944]
	mov edi, DWORD PTR [ebp+3948]
	mov edx, DWORD PTR [ebp+3872]
	xor edx, DWORD PTR [ebp+3908]
	and edx, eax
	xor edx, DWORD PTR [ebp+3872]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3876]
	xor edx, DWORD PTR [ebp+3912]
	and edx, eax
	xor edx, DWORD PTR [ebp+3876]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3880]
	xor edx, DWORD PTR [ebp+3916]
	and edx, eax
	xor edx, DWORD PTR [ebp+3880]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3884]
	xor edx, DWORD PTR [ebp+3920]
	and edx, eax
	xor edx, DWORD PTR [ebp+3884]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3888]
	xor edx, DWORD PTR [ebp+3924]
	and edx, eax
	xor edx, DWORD PTR [ebp+3888]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3892]
	xor edx, DWORD PTR [ebp+3928]
	and edx, eax
	xor edx, DWORD PTR [ebp+3892]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3896]
	xor edx, DWORD PTR [ebp+3932]
	and edx, eax
	xor edx, DWORD PTR [ebp+3896]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3900]
	xor edx, DWORD PTR [ebp+3936]
	and edx, eax
	xor edx, DWORD PTR [ebp+3900]
	mov DWORD PTR [ecx+28], edx
	mov ebx, DWORD PTR [ebp+3940]
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6

vg_brainpoolp256r1_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3840]
	sub eax, -1756866905
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, -1877078398
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, -1251891465
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, -1942390109
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, -1652322959
	mov DWORD PTR [ebp+3924], eax
	mov eax, DWORD PTR [ebp+3860]
	sbb eax, 1046874768
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3864]
	sbb eax, -1578194500
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3868]
	sbb eax, -1443145765
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3872]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3840]
	xor edx, DWORD PTR [ebp+3908]
	and edx, eax
	xor edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	xor edx, DWORD PTR [ebp+3912]
	and edx, eax
	xor edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	xor edx, DWORD PTR [ebp+3916]
	and edx, eax
	xor edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	xor edx, DWORD PTR [ebp+3920]
	and edx, eax
	xor edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	xor edx, DWORD PTR [ebp+3924]
	and edx, eax
	xor edx, DWORD PTR [ebp+3856]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	xor edx, DWORD PTR [ebp+3928]
	and edx, eax
	xor edx, DWORD PTR [ebp+3860]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	xor edx, DWORD PTR [ebp+3932]
	and edx, eax
	xor edx, DWORD PTR [ebp+3864]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	xor edx, DWORD PTR [ebp+3936]
	and edx, eax
	xor edx, DWORD PTR [ebp+3868]
	mov DWORD PTR [ecx+28], edx
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6

vg_brainpoolp256r1_sub_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	sbb eax, eax
	mov edx, -1756866905
	and edx, eax
	mov DWORD PTR [ebp+3908], edx
	mov edx, -1877078398
	and edx, eax
	mov DWORD PTR [ebp+3912], edx
	mov edx, -1251891465
	and edx, eax
	mov DWORD PTR [ebp+3916], edx
	mov edx, -1942390109
	and edx, eax
	mov DWORD PTR [ebp+3920], edx
	mov edx, -1652322959
	and edx, eax
	mov DWORD PTR [ebp+3924], edx
	mov edx, 1046874768
	and edx, eax
	mov DWORD PTR [ebp+3928], edx
	mov edx, -1578194500
	and edx, eax
	mov DWORD PTR [ebp+3932], edx
	mov edx, -1443145765
	and edx, eax
	mov DWORD PTR [ebp+3936], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3840]
	add edx, DWORD PTR [ebp+3908]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	adc edx, DWORD PTR [ebp+3912]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	adc edx, DWORD PTR [ebp+3916]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	adc edx, DWORD PTR [ebp+3920]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	adc edx, DWORD PTR [ebp+3924]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	adc edx, DWORD PTR [ebp+3928]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	adc edx, DWORD PTR [ebp+3932]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	adc edx, DWORD PTR [ebp+3936]
	mov DWORD PTR [ecx+28], edx
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6
