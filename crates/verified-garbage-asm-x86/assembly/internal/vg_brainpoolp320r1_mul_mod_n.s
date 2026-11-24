// The functions of `src/internal/vg_brainpoolp320r1_mul_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3900], ebx
	mov DWORD PTR [eax+3904], esi
	mov DWORD PTR [eax+3908], edi
	mov DWORD PTR [eax+3912], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	cmp edi, esi
	je 20f
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3812], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+3868], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [ebp+3896], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3816], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3820], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3824], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3828], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3832], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3836], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3840], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3844], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3848], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3860]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3852], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3864]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3816], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3868]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3820], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3872]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3824], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3876]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3828], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3880]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3832], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3884]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3836], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3888]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3840], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3892]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3844], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3896]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3848], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3852], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3856], ebx
	mov ebp, edi
	jmp 21f
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3812], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3816], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3780]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3820], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3784]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3780]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3824], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3788]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3784]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3828], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3792]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3788]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3784]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3832], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3792]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3788]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3836], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3792]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3788]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3840], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3792]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3844], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3792]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3848], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3776]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3816]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, -60669425
	mul edx
	mov DWORD PTR [edi+3852], eax
	mov edx, 1153798929
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3780]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3796]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3820]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -2037295781
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3816], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3784]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3824]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -293185303
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3820], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3788]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3800]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3828]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, 759705287
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3824], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3792]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3832]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -1232137565
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3828], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3796]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3804]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3836]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -108015707
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3832], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3800]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3840]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -771628955
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3836], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3804]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3808]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3844]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -516130722
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3840], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3808]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3848]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, 918310839
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3844], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3812]
	mov edx, DWORD PTR [edi+3812]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3852]
	mov edx, -748796128
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3848], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3852], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3856], ebx
	mov ebp, edi
21:
	mov eax, DWORD PTR [ebp+3816]
	sub eax, 1153798929
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ebp+3820]
	sbb eax, -2037295781
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ebp+3824]
	sbb eax, -293185303
	mov DWORD PTR [ebp+3868], eax
	mov eax, DWORD PTR [ebp+3828]
	sbb eax, 759705287
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3832]
	sbb eax, -1232137565
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3836]
	sbb eax, -108015707
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3840]
	sbb eax, -771628955
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, -516130722
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, 918310839
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, -748796128
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3904]
	mov edi, DWORD PTR [ebp+3908]
	mov edx, DWORD PTR [ebp+3816]
	xor edx, DWORD PTR [ebp+3860]
	and edx, eax
	xor edx, DWORD PTR [ebp+3816]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3820]
	xor edx, DWORD PTR [ebp+3864]
	and edx, eax
	xor edx, DWORD PTR [ebp+3820]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3824]
	xor edx, DWORD PTR [ebp+3868]
	and edx, eax
	xor edx, DWORD PTR [ebp+3824]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3828]
	xor edx, DWORD PTR [ebp+3872]
	and edx, eax
	xor edx, DWORD PTR [ebp+3828]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3832]
	xor edx, DWORD PTR [ebp+3876]
	and edx, eax
	xor edx, DWORD PTR [ebp+3832]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3836]
	xor edx, DWORD PTR [ebp+3880]
	and edx, eax
	xor edx, DWORD PTR [ebp+3836]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3840]
	xor edx, DWORD PTR [ebp+3884]
	and edx, eax
	xor edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3844]
	xor edx, DWORD PTR [ebp+3888]
	and edx, eax
	xor edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3848]
	xor edx, DWORD PTR [ebp+3892]
	and edx, eax
	xor edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3852]
	xor edx, DWORD PTR [ebp+3896]
	and edx, eax
	xor edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+36], edx
	mov ebx, DWORD PTR [ebp+3900]
	mov ebp, DWORD PTR [ebp+3912]
	ret
	.p2align 6
