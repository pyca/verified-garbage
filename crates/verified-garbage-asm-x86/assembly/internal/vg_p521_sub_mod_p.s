// The functions of `src/internal/vg_p521_sub_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sub_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3752], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3520], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3524], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3528], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3532], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3536], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3540], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3544], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3548], eax
	mov eax, DWORD PTR [ecx+32]
	sbb eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3552], eax
	mov eax, DWORD PTR [ecx+36]
	sbb eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3556], eax
	mov eax, DWORD PTR [ecx+40]
	sbb eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3560], eax
	mov eax, DWORD PTR [ecx+44]
	sbb eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3564], eax
	mov eax, DWORD PTR [ecx+48]
	sbb eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3568], eax
	mov eax, DWORD PTR [ecx+52]
	sbb eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3572], eax
	mov eax, DWORD PTR [ecx+56]
	sbb eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3576], eax
	mov eax, DWORD PTR [ecx+60]
	sbb eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3580], eax
	mov eax, DWORD PTR [ecx+64]
	sbb eax, DWORD PTR [edx+64]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+68]
	sbb eax, DWORD PTR [edx+68]
	mov DWORD PTR [ebp+3588], eax
	sbb eax, eax
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3668], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3672], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3676], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3680], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3684], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3688], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3692], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3696], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3700], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3704], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3708], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3712], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3716], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3720], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3724], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3728], edx
	mov edx, 511
	and edx, eax
	mov DWORD PTR [ebp+3732], edx
	mov edx, 0
	and edx, eax
	mov DWORD PTR [ebp+3736], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3520]
	add edx, DWORD PTR [ebp+3668]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3524]
	adc edx, DWORD PTR [ebp+3672]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3528]
	adc edx, DWORD PTR [ebp+3676]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3532]
	adc edx, DWORD PTR [ebp+3680]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3536]
	adc edx, DWORD PTR [ebp+3684]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3540]
	adc edx, DWORD PTR [ebp+3688]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3544]
	adc edx, DWORD PTR [ebp+3692]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3548]
	adc edx, DWORD PTR [ebp+3696]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3552]
	adc edx, DWORD PTR [ebp+3700]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3556]
	adc edx, DWORD PTR [ebp+3704]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3560]
	adc edx, DWORD PTR [ebp+3708]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3564]
	adc edx, DWORD PTR [ebp+3712]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3568]
	adc edx, DWORD PTR [ebp+3716]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3572]
	adc edx, DWORD PTR [ebp+3720]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3576]
	adc edx, DWORD PTR [ebp+3724]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3580]
	adc edx, DWORD PTR [ebp+3728]
	mov DWORD PTR [ecx+60], edx
	mov edx, DWORD PTR [ebp+3584]
	adc edx, DWORD PTR [ebp+3732]
	mov DWORD PTR [ecx+64], edx
	mov edx, DWORD PTR [ebp+3588]
	adc edx, DWORD PTR [ebp+3736]
	mov DWORD PTR [ecx+68], edx
	mov ebp, DWORD PTR [ebp+3752]
	ret
	.p2align 6
