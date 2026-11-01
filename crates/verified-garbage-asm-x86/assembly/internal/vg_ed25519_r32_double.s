// The functions of `src/internal/vg_ed25519_r32_double.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r32_double:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+928], ebx
	mov DWORD PTR [eax+932], ebp
	mov DWORD PTR [eax+936], edi
	mov edi, eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+348], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+348], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+320], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+380], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+380], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+352], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+320]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+476], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+448]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+452]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+456]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+460]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+464]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+468]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+472]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+476]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+476], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+448], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+448]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+384]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+480], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+452]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+484], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+456]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+488], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+460]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+492], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+464]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+496], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+468]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+500], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+472]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+504], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+476]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+508], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+480]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+480], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+484]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+484], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+488]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+488], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+492]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+492], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+496]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+496], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+500]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+500], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+504]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+504], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+508]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+508], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+480], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+448]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+352]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+452]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+456]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+460]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+464]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+468]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+472]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+476]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+512]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+516]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+520]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+524]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+528]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+532]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+536]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+540]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+512], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+512]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+352]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+516]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+520]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+524]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+528]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+532]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+536]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+540]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+512]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+516]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+520]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+524]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+528]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+532]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+536]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+540]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+512], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+96], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+100], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+104], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+108], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+112], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+116], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+120], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+96], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+100], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+104], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+108], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+112], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+116], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+120], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+128], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+132], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+136], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+140], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+144], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+148], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+152], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+128]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+128], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+132]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+132], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+136]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+136], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+140]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+140], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+144]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+144], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+148]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+148], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+152]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+152], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+156]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+128], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+160], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+164], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+168], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+172], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+180], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+184], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+160]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+160], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+164]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+164], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+168]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+168], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+172]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+172], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+176]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+180]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+180], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+184]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+184], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+188]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov edx, edi
	mov ebx, DWORD PTR [edx+928]
	mov ebp, DWORD PTR [edx+932]
	mov edi, DWORD PTR [edx+936]
	ret
	.p2align 6
