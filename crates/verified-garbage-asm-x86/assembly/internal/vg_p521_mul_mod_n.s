// The functions of `src/internal/vg_p521_mul_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3740], ebx
	mov DWORD PTR [eax+3744], esi
	mov DWORD PTR [eax+3748], edi
	mov DWORD PTR [eax+3752], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3520], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3524], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3592], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ebp+3520]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3520]
	adc edx, 0
	mov DWORD PTR [ebp+3520], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3524]
	adc edx, 0
	mov DWORD PTR [ebp+3524], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3528]
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3592]
	add eax, ebx
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ebp+3596]
	adc eax, 0
	mov DWORD PTR [ebp+3596], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3524]
	adc edx, 0
	mov DWORD PTR [ebp+3524], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3528]
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3596]
	add eax, ebx
	mov DWORD PTR [ebp+3596], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ebp+3524]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3524]
	adc edx, 0
	mov DWORD PTR [ebp+3524], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3528]
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3596]
	add eax, ebx
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ebp+3600]
	adc eax, 0
	mov DWORD PTR [ebp+3600], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3528]
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3600]
	add eax, ebx
	mov DWORD PTR [ebp+3600], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ebp+3528]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3528]
	adc edx, 0
	mov DWORD PTR [ebp+3528], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3600]
	add eax, ebx
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ebp+3604]
	adc eax, 0
	mov DWORD PTR [ebp+3604], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3604]
	add eax, ebx
	mov DWORD PTR [ebp+3604], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ebp+3532]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3532]
	adc edx, 0
	mov DWORD PTR [ebp+3532], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3604]
	add eax, ebx
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ebp+3608]
	adc eax, 0
	mov DWORD PTR [ebp+3608], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3608]
	add eax, ebx
	mov DWORD PTR [ebp+3608], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ebp+3536]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3536]
	adc edx, 0
	mov DWORD PTR [ebp+3536], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3608]
	add eax, ebx
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ebp+3612]
	adc eax, 0
	mov DWORD PTR [ebp+3612], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3612]
	add eax, ebx
	mov DWORD PTR [ebp+3612], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ebp+3540]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3540]
	adc edx, 0
	mov DWORD PTR [ebp+3540], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3612]
	add eax, ebx
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ebp+3616]
	adc eax, 0
	mov DWORD PTR [ebp+3616], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3616]
	add eax, ebx
	mov DWORD PTR [ebp+3616], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ebp+3544]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3544]
	adc edx, 0
	mov DWORD PTR [ebp+3544], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3616]
	add eax, ebx
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ebp+3620]
	adc eax, 0
	mov DWORD PTR [ebp+3620], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3620]
	add eax, ebx
	mov DWORD PTR [ebp+3620], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ebp+3548]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3548]
	adc edx, 0
	mov DWORD PTR [ebp+3548], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3620]
	add eax, ebx
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ebp+3624]
	adc eax, 0
	mov DWORD PTR [ebp+3624], eax
	mov ecx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3624]
	add eax, ebx
	mov DWORD PTR [ebp+3624], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ebp+3552]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3552]
	adc edx, 0
	mov DWORD PTR [ebp+3552], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3624]
	add eax, ebx
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ebp+3628]
	adc eax, 0
	mov DWORD PTR [ebp+3628], eax
	mov ecx, DWORD PTR [edi+36]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3628]
	add eax, ebx
	mov DWORD PTR [ebp+3628], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ebp+3556]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3556]
	adc edx, 0
	mov DWORD PTR [ebp+3556], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3628]
	add eax, ebx
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ebp+3632]
	adc eax, 0
	mov DWORD PTR [ebp+3632], eax
	mov ecx, DWORD PTR [edi+40]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3632]
	add eax, ebx
	mov DWORD PTR [ebp+3632], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ebp+3560]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3560]
	adc edx, 0
	mov DWORD PTR [ebp+3560], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3632]
	add eax, ebx
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ebp+3636]
	adc eax, 0
	mov DWORD PTR [ebp+3636], eax
	mov ecx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3636]
	add eax, ebx
	mov DWORD PTR [ebp+3636], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ebp+3564]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3564]
	adc edx, 0
	mov DWORD PTR [ebp+3564], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3636]
	add eax, ebx
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ebp+3640]
	adc eax, 0
	mov DWORD PTR [ebp+3640], eax
	mov ecx, DWORD PTR [edi+48]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3640]
	add eax, ebx
	mov DWORD PTR [ebp+3640], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3644], eax
	mov eax, DWORD PTR [ebp+3568]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3568]
	adc edx, 0
	mov DWORD PTR [ebp+3568], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3640]
	add eax, ebx
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ebp+3644]
	adc eax, 0
	mov DWORD PTR [ebp+3644], eax
	mov ecx, DWORD PTR [edi+52]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3644]
	add eax, ebx
	mov DWORD PTR [ebp+3644], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3572]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3572]
	adc edx, 0
	mov DWORD PTR [ebp+3572], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3644]
	add eax, ebx
	mov DWORD PTR [ebp+3644], eax
	mov eax, DWORD PTR [ebp+3648]
	adc eax, 0
	mov DWORD PTR [ebp+3648], eax
	mov ecx, DWORD PTR [edi+56]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3648]
	add eax, ebx
	mov DWORD PTR [ebp+3648], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3576]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3576]
	adc edx, 0
	mov DWORD PTR [ebp+3576], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3648]
	add eax, ebx
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3652]
	adc eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov ecx, DWORD PTR [edi+60]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3580]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3580]
	adc edx, 0
	mov DWORD PTR [ebp+3580], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3656]
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov ecx, DWORD PTR [edi+64]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3584]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3660]
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov ecx, DWORD PTR [edi+68]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3588]
	mov ecx, 2041157063
	mul ecx
	mov ecx, eax
	mov eax, -1858575351
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1150306530
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1986246738
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 1001769400
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -150362672
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 2144076104
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1087400341
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1367771011
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -6
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 511
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 0
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3664]
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3592]
	sub eax, -1858575351
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3596]
	sbb eax, -1150306530
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3600]
	sbb eax, -1986246738
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3604]
	sbb eax, 1001769400
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3608]
	sbb eax, -150362672
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3612]
	sbb eax, 2144076104
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3616]
	sbb eax, -1087400341
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3620]
	sbb eax, 1367771011
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3624]
	sbb eax, -6
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3628]
	sbb eax, -1
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3632]
	sbb eax, -1
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3636]
	sbb eax, -1
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3640]
	sbb eax, -1
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3644]
	sbb eax, -1
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3648]
	sbb eax, -1
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3652]
	sbb eax, -1
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3656]
	sbb eax, 511
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3660]
	sbb eax, 0
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3664]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3744]
	mov edi, DWORD PTR [ebp+3748]
	mov edx, DWORD PTR [ebp+3592]
	xor edx, DWORD PTR [ebp+3668]
	and edx, eax
	xor edx, DWORD PTR [ebp+3592]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3596]
	xor edx, DWORD PTR [ebp+3672]
	and edx, eax
	xor edx, DWORD PTR [ebp+3596]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3600]
	xor edx, DWORD PTR [ebp+3676]
	and edx, eax
	xor edx, DWORD PTR [ebp+3600]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3604]
	xor edx, DWORD PTR [ebp+3680]
	and edx, eax
	xor edx, DWORD PTR [ebp+3604]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3608]
	xor edx, DWORD PTR [ebp+3684]
	and edx, eax
	xor edx, DWORD PTR [ebp+3608]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3612]
	xor edx, DWORD PTR [ebp+3688]
	and edx, eax
	xor edx, DWORD PTR [ebp+3612]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3616]
	xor edx, DWORD PTR [ebp+3692]
	and edx, eax
	xor edx, DWORD PTR [ebp+3616]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3620]
	xor edx, DWORD PTR [ebp+3696]
	and edx, eax
	xor edx, DWORD PTR [ebp+3620]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3624]
	xor edx, DWORD PTR [ebp+3700]
	and edx, eax
	xor edx, DWORD PTR [ebp+3624]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3628]
	xor edx, DWORD PTR [ebp+3704]
	and edx, eax
	xor edx, DWORD PTR [ebp+3628]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3632]
	xor edx, DWORD PTR [ebp+3708]
	and edx, eax
	xor edx, DWORD PTR [ebp+3632]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3636]
	xor edx, DWORD PTR [ebp+3712]
	and edx, eax
	xor edx, DWORD PTR [ebp+3636]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3640]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3640]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3644]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3644]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3648]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3648]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3652]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3652]
	mov DWORD PTR [ecx+60], edx
	mov edx, DWORD PTR [ebp+3656]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3656]
	mov DWORD PTR [ecx+64], edx
	mov edx, DWORD PTR [ebp+3660]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3660]
	mov DWORD PTR [ecx+68], edx
	mov ebx, DWORD PTR [ebp+3740]
	mov ebp, DWORD PTR [ebp+3752]
	ret
	.p2align 6
