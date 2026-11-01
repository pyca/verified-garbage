// The functions of `src/internal/vg_p521_add_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_add_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3752], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3520], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3524], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3528], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3532], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3536], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3540], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3544], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3548], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3552], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3556], eax
	mov eax, DWORD PTR [ecx+40]
	adc eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3560], eax
	mov eax, DWORD PTR [ecx+44]
	adc eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3564], eax
	mov eax, DWORD PTR [ecx+48]
	adc eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3568], eax
	mov eax, DWORD PTR [ecx+52]
	adc eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3572], eax
	mov eax, DWORD PTR [ecx+56]
	adc eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3576], eax
	mov eax, DWORD PTR [ecx+60]
	adc eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3580], eax
	mov eax, DWORD PTR [ecx+64]
	adc eax, DWORD PTR [edx+64]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+68]
	adc eax, DWORD PTR [edx+68]
	mov DWORD PTR [ebp+3588], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ebp+3520]
	sub eax, -1
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3524]
	sbb eax, -1
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3528]
	sbb eax, -1
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3532]
	sbb eax, -1
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3536]
	sbb eax, -1
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3540]
	sbb eax, -1
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3544]
	sbb eax, -1
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3548]
	sbb eax, -1
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3552]
	sbb eax, -1
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3556]
	sbb eax, -1
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3560]
	sbb eax, -1
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3564]
	sbb eax, -1
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3568]
	sbb eax, -1
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3572]
	sbb eax, -1
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3576]
	sbb eax, -1
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3580]
	sbb eax, -1
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3584]
	sbb eax, 511
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3588]
	sbb eax, 0
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3592]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3520]
	xor edx, DWORD PTR [ebp+3668]
	and edx, eax
	xor edx, DWORD PTR [ebp+3520]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3524]
	xor edx, DWORD PTR [ebp+3672]
	and edx, eax
	xor edx, DWORD PTR [ebp+3524]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3528]
	xor edx, DWORD PTR [ebp+3676]
	and edx, eax
	xor edx, DWORD PTR [ebp+3528]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3532]
	xor edx, DWORD PTR [ebp+3680]
	and edx, eax
	xor edx, DWORD PTR [ebp+3532]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3536]
	xor edx, DWORD PTR [ebp+3684]
	and edx, eax
	xor edx, DWORD PTR [ebp+3536]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3540]
	xor edx, DWORD PTR [ebp+3688]
	and edx, eax
	xor edx, DWORD PTR [ebp+3540]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3544]
	xor edx, DWORD PTR [ebp+3692]
	and edx, eax
	xor edx, DWORD PTR [ebp+3544]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3548]
	xor edx, DWORD PTR [ebp+3696]
	and edx, eax
	xor edx, DWORD PTR [ebp+3548]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3552]
	xor edx, DWORD PTR [ebp+3700]
	and edx, eax
	xor edx, DWORD PTR [ebp+3552]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3556]
	xor edx, DWORD PTR [ebp+3704]
	and edx, eax
	xor edx, DWORD PTR [ebp+3556]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3560]
	xor edx, DWORD PTR [ebp+3708]
	and edx, eax
	xor edx, DWORD PTR [ebp+3560]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3564]
	xor edx, DWORD PTR [ebp+3712]
	and edx, eax
	xor edx, DWORD PTR [ebp+3564]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3568]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3568]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3572]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3572]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3576]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3576]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3580]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3580]
	mov DWORD PTR [ecx+60], edx
	mov edx, DWORD PTR [ebp+3584]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3584]
	mov DWORD PTR [ecx+64], edx
	mov edx, DWORD PTR [ebp+3588]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3588]
	mov DWORD PTR [ecx+68], edx
	mov ebp, DWORD PTR [ebp+3752]
	ret
	.p2align 6
