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
	cmp edi, esi
	je 20f
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3520], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3524], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3528], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3532], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3536], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3540], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3544], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3548], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3552], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3556], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3560], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3564], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebp+3568], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [ebp+3572], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [ebp+3576], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [ebp+3580], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [ebp+3736], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3592], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3596], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3600], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3604], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3608], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3612], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3616], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3620], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3624], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3628], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3632], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3636], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3640], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3644], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3648], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3652], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3656], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3660], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3592], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3596], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3600], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3604], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3608], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3612], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3696]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3616], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3700]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3620], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3704]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3624], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3708]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3628], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3712]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3632], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3636], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3640], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3644], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3664], ebx
	mov ebp, edi
	jmp 21f
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3520], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3524], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3528], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3532], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3536], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3540], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3544], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3548], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3552], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3556], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3560], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3564], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebp+3568], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [ebp+3572], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [ebp+3576], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [ebp+3580], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [ebp+3588], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3592], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3524]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3596], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3528]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3600], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3532]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3528]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3604], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3536]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3532]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3608], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3536]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3532]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3612], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3536]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3616], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3536]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3620], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3624], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3628], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3632], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3636], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3640], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3644], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3648], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3652], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3656], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3520]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 2041157063
	mul edx
	mov DWORD PTR [edi+3660], eax
	mov edx, -1858575351
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3524]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1150306530
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3592], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3528]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1986246738
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3596], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3532]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1001769400
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3600], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3536]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -150362672
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3604], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3540]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 2144076104
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3608], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3544]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1087400341
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3612], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3548]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1367771011
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3616], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3552]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -6
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3620], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3556]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3624], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3560]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3628], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3564]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3576]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3632], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3568]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3636], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3572]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3580]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3640], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3576]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3644], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3580]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 511
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3664], ebx
	mov ebp, edi
21:
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
