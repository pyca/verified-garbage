// The functions of `src/internal/vg_ed25519_r32_point_add.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r32_point_add:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+928], ebx
	mov DWORD PTR [eax+932], ebp
	mov DWORD PTR [eax+936], edi
	mov edi, eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+96]
	sbb eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+100]
	sbb eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+104]
	sbb eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+108]
	sbb eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+112]
	sbb eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+116]
	sbb eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+120]
	sbb eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+124]
	sbb eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+348], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+320]
	sbb eax, ecx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+324]
	sbb eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+328]
	sbb eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+332]
	sbb eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+336]
	sbb eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	sbb eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	sbb eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	sbb eax, 0
	mov DWORD PTR [edi+348], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+320]
	sbb eax, ecx
	mov DWORD PTR [edi+320], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+224]
	sbb eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+228]
	sbb eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+232]
	sbb eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+236]
	sbb eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+240]
	sbb eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+244]
	sbb eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+248]
	sbb eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+252]
	sbb eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	sbb eax, ecx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	sbb eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	sbb eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	sbb eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+368]
	sbb eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+372]
	sbb eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+376]
	sbb eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+380]
	sbb eax, 0
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	sbb eax, ecx
	mov DWORD PTR [edi+352], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+380]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+320], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+324], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+328], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+332], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+336], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+340], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+344], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+348], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+324]
	adc eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+328]
	adc eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+332]
	adc eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+336]
	adc eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	adc eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	adc eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	adc eax, 0
	mov DWORD PTR [edi+348], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+96]
	adc eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+100]
	adc eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+104]
	adc eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+108]
	adc eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+112]
	adc eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+116]
	adc eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+120]
	adc eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+124]
	adc eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	adc eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	adc eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	adc eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+368]
	adc eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+372]
	adc eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+376]
	adc eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+380]
	adc eax, 0
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+224]
	adc eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+228]
	adc eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+232]
	adc eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+236]
	adc eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+240]
	adc eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+244]
	adc eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+248]
	adc eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+252]
	adc eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+412]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+352], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+356], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+360], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+364], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+368], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+372], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+376], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+380], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	adc eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	adc eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	adc eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+368]
	adc eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+372]
	adc eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+376]
	adc eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+380]
	adc eax, 0
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+604]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+384], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+388], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+392], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+396], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+400], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+404], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+408], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+412], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+384]
	adc eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+316]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+384], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+388], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+392], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+396], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+400], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+404], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+408], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+412], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+128]
	adc eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+132]
	adc eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+136]
	adc eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+140]
	adc eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+144]
	adc eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+148]
	adc eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+152]
	adc eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+156]
	adc eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+420]
	adc eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+424]
	adc eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+428]
	adc eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+432]
	adc eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+436]
	adc eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+440]
	adc eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+444]
	adc eax, 0
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+284]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+416], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+420], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+424], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+428], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+432], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+436], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+440], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+444], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+420]
	adc eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+424]
	adc eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+428]
	adc eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+432]
	adc eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+436]
	adc eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+440]
	adc eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+444]
	adc eax, 0
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+352]
	sbb eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+356]
	sbb eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+360]
	sbb eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+364]
	sbb eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+368]
	sbb eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+372]
	sbb eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+376]
	sbb eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+380]
	sbb eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+476], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+448]
	sbb eax, ecx
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+452]
	sbb eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+456]
	sbb eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+460]
	sbb eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+464]
	sbb eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+468]
	sbb eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+472]
	sbb eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+476]
	sbb eax, 0
	mov DWORD PTR [edi+476], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+448]
	sbb eax, ecx
	mov DWORD PTR [edi+448], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+416]
	sbb eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+420]
	sbb eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+424]
	sbb eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+428]
	sbb eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+432]
	sbb eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+436]
	sbb eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+440]
	sbb eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+444]
	sbb eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+508], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+480]
	sbb eax, ecx
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+484]
	sbb eax, 0
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+488]
	sbb eax, 0
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+492]
	sbb eax, 0
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+496]
	sbb eax, 0
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+500]
	sbb eax, 0
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+504]
	sbb eax, 0
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+508]
	sbb eax, 0
	mov DWORD PTR [edi+508], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+480]
	sbb eax, ecx
	mov DWORD PTR [edi+480], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+416]
	adc eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+420]
	adc eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+424]
	adc eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+428]
	adc eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+432]
	adc eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+436]
	adc eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+440]
	adc eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+444]
	adc eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+540], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+512]
	adc eax, ecx
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+516]
	adc eax, 0
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+520]
	adc eax, 0
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+524]
	adc eax, 0
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+528]
	adc eax, 0
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+532]
	adc eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+536]
	adc eax, 0
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+540]
	adc eax, 0
	mov DWORD PTR [edi+540], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+512]
	adc eax, ecx
	mov DWORD PTR [edi+512], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+352]
	adc eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+356]
	adc eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+360]
	adc eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+364]
	adc eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+368]
	adc eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+372]
	adc eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+376]
	adc eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+380]
	adc eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+548]
	adc eax, 0
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+552]
	adc eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+556]
	adc eax, 0
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+560]
	adc eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+564]
	adc eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+568]
	adc eax, 0
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	adc eax, 0
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+476]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+64], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+68], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+72], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+76], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+80], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+84], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+88], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+92], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	adc eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	adc eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	adc eax, 0
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	adc eax, 0
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	adc eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	adc eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	adc eax, 0
	mov DWORD PTR [edi+92], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+572]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+96], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+100], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+104], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+108], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+112], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+116], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+120], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+124], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+96]
	adc eax, ecx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+100]
	adc eax, 0
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+104]
	adc eax, 0
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+108]
	adc eax, 0
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+112]
	adc eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	adc eax, 0
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+120]
	adc eax, 0
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+124]
	adc eax, 0
	mov DWORD PTR [edi+124], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+96]
	adc eax, ecx
	mov DWORD PTR [edi+96], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+508]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+128], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+132], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+136], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+140], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+144], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+148], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+152], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+156], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+128]
	adc eax, ecx
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+132]
	adc eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+136]
	adc eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+140]
	adc eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+144]
	adc eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+148]
	adc eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+152]
	adc eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+156]
	adc eax, 0
	mov DWORD PTR [edi+156], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+128]
	adc eax, ecx
	mov DWORD PTR [edi+128], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+572]
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
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+160], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+164], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+168], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+172], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+176], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+180], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+184], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+188], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+160]
	adc eax, ecx
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	adc eax, 0
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	adc eax, 0
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	adc eax, 0
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	adc eax, 0
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	adc eax, 0
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	adc eax, 0
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	adc eax, 0
	mov DWORD PTR [edi+188], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+160]
	adc eax, ecx
	mov DWORD PTR [edi+160], eax
	mov edx, edi
	mov ebx, DWORD PTR [edx+928]
	mov ebp, DWORD PTR [edx+932]
	mov edi, DWORD PTR [edx+936]
	ret
	.p2align 6
