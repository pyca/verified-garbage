// The functions of `src/internal/vg_gf25519_r32_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r32_mul:
	mov DWORD PTR [edi+928], ebx
	mov DWORD PTR [edi+932], esi
	mov DWORD PTR [edi+936], edi
	mov DWORD PTR [edi+940], ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+732]
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
	mov DWORD PTR [edi+672], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+676], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+680], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+684], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+688], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+692], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+696], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+700], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+672]
	adc eax, ecx
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+676]
	adc eax, 0
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+680]
	adc eax, 0
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+684]
	adc eax, 0
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+688]
	adc eax, 0
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+692]
	adc eax, 0
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+696]
	adc eax, 0
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+700]
	adc eax, 0
	mov DWORD PTR [edi+700], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+672]
	adc eax, ecx
	mov DWORD PTR [edi+672], eax
	mov edx, edi
	mov ebx, DWORD PTR [edx+928]
	mov esi, DWORD PTR [edx+932]
	mov ebp, DWORD PTR [edx+940]
	mov edi, DWORD PTR [edx+936]
	ret
	.p2align 6
