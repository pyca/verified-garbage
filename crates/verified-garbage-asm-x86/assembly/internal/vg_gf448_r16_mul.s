// The functions of `src/internal/vg_gf448_r16_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r16_mul:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+16]
	add esi, edi
	mov ebp, DWORD PTR [esp+12]
	add ebp, edi
	mov eax, 0
	mov DWORD PTR [edi+3584], eax
	mov DWORD PTR [edi+3588], eax
	mov DWORD PTR [edi+3592], eax
	mov DWORD PTR [edi+3596], eax
	mov DWORD PTR [edi+3600], eax
	mov DWORD PTR [edi+3604], eax
	mov DWORD PTR [edi+3608], eax
	mov DWORD PTR [edi+3612], eax
	mov DWORD PTR [edi+3616], eax
	mov DWORD PTR [edi+3620], eax
	mov DWORD PTR [edi+3624], eax
	mov DWORD PTR [edi+3628], eax
	mov DWORD PTR [edi+3632], eax
	mov DWORD PTR [edi+3636], eax
	mov DWORD PTR [edi+3640], eax
	mov DWORD PTR [edi+3644], eax
	mov DWORD PTR [edi+3648], eax
	mov DWORD PTR [edi+3652], eax
	mov DWORD PTR [edi+3656], eax
	mov DWORD PTR [edi+3660], eax
	mov DWORD PTR [edi+3664], eax
	mov DWORD PTR [edi+3668], eax
	mov DWORD PTR [edi+3672], eax
	mov DWORD PTR [edi+3676], eax
	mov DWORD PTR [edi+3680], eax
	mov DWORD PTR [edi+3684], eax
	mov DWORD PTR [edi+3688], eax
	mov DWORD PTR [edi+3692], eax
	mov ecx, DWORD PTR [ebp]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3584]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3584], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3588]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3588], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3592], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3596], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov DWORD PTR [edi+3696], ebx
	mov ecx, DWORD PTR [ebp+4]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3588]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3588], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3592], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3596], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov DWORD PTR [edi+3700], ebx
	mov ecx, DWORD PTR [ebp+8]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3592]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3592], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3596], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov DWORD PTR [edi+3704], ebx
	mov ecx, DWORD PTR [ebp+12]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3596]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3596], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov DWORD PTR [edi+3708], ebx
	mov ecx, DWORD PTR [ebp+16]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3600]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3600], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov DWORD PTR [edi+3712], ebx
	mov ecx, DWORD PTR [ebp+20]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3604]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3604], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov DWORD PTR [edi+3716], ebx
	mov ecx, DWORD PTR [ebp+24]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3608]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3608], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov DWORD PTR [edi+3720], ebx
	mov ecx, DWORD PTR [ebp+28]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3612]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3612], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov DWORD PTR [edi+3724], ebx
	mov ecx, DWORD PTR [ebp+32]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3616]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3616], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov DWORD PTR [edi+3728], ebx
	mov ecx, DWORD PTR [ebp+36]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3620]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3620], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov DWORD PTR [edi+3732], ebx
	mov ecx, DWORD PTR [ebp+40]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3624]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3624], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov DWORD PTR [edi+3736], ebx
	mov ecx, DWORD PTR [ebp+44]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3628]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3628], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov DWORD PTR [edi+3740], ebx
	mov ecx, DWORD PTR [ebp+48]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3632]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3632], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov DWORD PTR [edi+3744], ebx
	mov ecx, DWORD PTR [ebp+52]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3636]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3636], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov DWORD PTR [edi+3748], ebx
	mov ecx, DWORD PTR [ebp+56]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3640]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3640], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov DWORD PTR [edi+3752], ebx
	mov ecx, DWORD PTR [ebp+60]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3644]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3644], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov DWORD PTR [edi+3756], ebx
	mov ecx, DWORD PTR [ebp+64]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3648]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3648], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov DWORD PTR [edi+3760], ebx
	mov ecx, DWORD PTR [ebp+68]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3652]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3652], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov DWORD PTR [edi+3764], ebx
	mov ecx, DWORD PTR [ebp+72]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3656]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3656], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov DWORD PTR [edi+3768], ebx
	mov ecx, DWORD PTR [ebp+76]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3660]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3660], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov DWORD PTR [edi+3772], ebx
	mov ecx, DWORD PTR [ebp+80]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3664]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3664], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov DWORD PTR [edi+3776], ebx
	mov ecx, DWORD PTR [ebp+84]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3668]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3668], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov DWORD PTR [edi+3780], ebx
	mov ecx, DWORD PTR [ebp+88]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3672]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3672], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov DWORD PTR [edi+3784], ebx
	mov ecx, DWORD PTR [ebp+92]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3676]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3676], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3784]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3784], edx
	shr ebx, 16
	mov DWORD PTR [edi+3788], ebx
	mov ecx, DWORD PTR [ebp+96]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3680]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3680], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3784]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3784], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3788]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3788], edx
	shr ebx, 16
	mov DWORD PTR [edi+3792], ebx
	mov ecx, DWORD PTR [ebp+100]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3684]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3684], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3784]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3784], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3788]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3788], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3792]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3792], edx
	shr ebx, 16
	mov DWORD PTR [edi+3796], ebx
	mov ecx, DWORD PTR [ebp+104]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3688]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3688], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3784]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3784], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3788]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3788], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3792]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3792], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3796]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3796], edx
	shr ebx, 16
	mov DWORD PTR [edi+3800], ebx
	mov ecx, DWORD PTR [ebp+108]
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [edi+3692]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3692], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, DWORD PTR [edi+3696]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3696], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, DWORD PTR [edi+3700]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3700], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, DWORD PTR [edi+3704]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3704], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, DWORD PTR [edi+3708]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3708], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, DWORD PTR [edi+3712]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3712], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, DWORD PTR [edi+3716]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3716], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, DWORD PTR [edi+3720]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3720], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, DWORD PTR [edi+3724]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3724], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, DWORD PTR [edi+3728]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3728], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, DWORD PTR [edi+3732]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3732], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, DWORD PTR [edi+3736]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3736], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, DWORD PTR [edi+3740]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3740], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, DWORD PTR [edi+3744]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3744], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, DWORD PTR [edi+3748]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3748], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, DWORD PTR [edi+3752]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3752], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+64]
	mul ecx
	add eax, DWORD PTR [edi+3756]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3756], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+68]
	mul ecx
	add eax, DWORD PTR [edi+3760]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3760], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+72]
	mul ecx
	add eax, DWORD PTR [edi+3764]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3764], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+76]
	mul ecx
	add eax, DWORD PTR [edi+3768]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3768], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+80]
	mul ecx
	add eax, DWORD PTR [edi+3772]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3772], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+84]
	mul ecx
	add eax, DWORD PTR [edi+3776]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3776], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+88]
	mul ecx
	add eax, DWORD PTR [edi+3780]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3780], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+92]
	mul ecx
	add eax, DWORD PTR [edi+3784]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3784], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+96]
	mul ecx
	add eax, DWORD PTR [edi+3788]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3788], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+100]
	mul ecx
	add eax, DWORD PTR [edi+3792]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3792], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+104]
	mul ecx
	add eax, DWORD PTR [edi+3796]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3796], edx
	shr ebx, 16
	mov eax, DWORD PTR [esi+108]
	mul ecx
	add eax, DWORD PTR [edi+3800]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3800], edx
	shr ebx, 16
	mov DWORD PTR [edi+3804], ebx
	mov eax, DWORD PTR [edi+3584]
	add eax, DWORD PTR [edi+3696]
	add eax, DWORD PTR [edi+3752]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3588]
	add eax, DWORD PTR [edi+3700]
	add eax, DWORD PTR [edi+3756]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [edi+3592]
	add eax, DWORD PTR [edi+3704]
	add eax, DWORD PTR [edi+3760]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [edi+3596]
	add eax, DWORD PTR [edi+3708]
	add eax, DWORD PTR [edi+3764]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [edi+3600]
	add eax, DWORD PTR [edi+3712]
	add eax, DWORD PTR [edi+3768]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [edi+3604]
	add eax, DWORD PTR [edi+3716]
	add eax, DWORD PTR [edi+3772]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [edi+3608]
	add eax, DWORD PTR [edi+3720]
	add eax, DWORD PTR [edi+3776]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [edi+3612]
	add eax, DWORD PTR [edi+3724]
	add eax, DWORD PTR [edi+3780]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [edi+3616]
	add eax, DWORD PTR [edi+3728]
	add eax, DWORD PTR [edi+3784]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [edi+3620]
	add eax, DWORD PTR [edi+3732]
	add eax, DWORD PTR [edi+3788]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [edi+3624]
	add eax, DWORD PTR [edi+3736]
	add eax, DWORD PTR [edi+3792]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [edi+3628]
	add eax, DWORD PTR [edi+3740]
	add eax, DWORD PTR [edi+3796]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [edi+3632]
	add eax, DWORD PTR [edi+3744]
	add eax, DWORD PTR [edi+3800]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [edi+3636]
	add eax, DWORD PTR [edi+3748]
	add eax, DWORD PTR [edi+3804]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [edi+3640]
	add eax, DWORD PTR [edi+3752]
	add eax, DWORD PTR [edi+3696]
	add eax, DWORD PTR [edi+3752]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [edi+3644]
	add eax, DWORD PTR [edi+3756]
	add eax, DWORD PTR [edi+3700]
	add eax, DWORD PTR [edi+3756]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [edi+3648]
	add eax, DWORD PTR [edi+3760]
	add eax, DWORD PTR [edi+3704]
	add eax, DWORD PTR [edi+3760]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [edi+3652]
	add eax, DWORD PTR [edi+3764]
	add eax, DWORD PTR [edi+3708]
	add eax, DWORD PTR [edi+3764]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [edi+3656]
	add eax, DWORD PTR [edi+3768]
	add eax, DWORD PTR [edi+3712]
	add eax, DWORD PTR [edi+3768]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [edi+3660]
	add eax, DWORD PTR [edi+3772]
	add eax, DWORD PTR [edi+3716]
	add eax, DWORD PTR [edi+3772]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [edi+3664]
	add eax, DWORD PTR [edi+3776]
	add eax, DWORD PTR [edi+3720]
	add eax, DWORD PTR [edi+3776]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [edi+3668]
	add eax, DWORD PTR [edi+3780]
	add eax, DWORD PTR [edi+3724]
	add eax, DWORD PTR [edi+3780]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [edi+3672]
	add eax, DWORD PTR [edi+3784]
	add eax, DWORD PTR [edi+3728]
	add eax, DWORD PTR [edi+3784]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [edi+3676]
	add eax, DWORD PTR [edi+3788]
	add eax, DWORD PTR [edi+3732]
	add eax, DWORD PTR [edi+3788]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [edi+3680]
	add eax, DWORD PTR [edi+3792]
	add eax, DWORD PTR [edi+3736]
	add eax, DWORD PTR [edi+3792]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [edi+3684]
	add eax, DWORD PTR [edi+3796]
	add eax, DWORD PTR [edi+3740]
	add eax, DWORD PTR [edi+3796]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [edi+3688]
	add eax, DWORD PTR [edi+3800]
	add eax, DWORD PTR [edi+3744]
	add eax, DWORD PTR [edi+3800]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [edi+3692]
	add eax, DWORD PTR [edi+3804]
	add eax, DWORD PTR [edi+3748]
	add eax, DWORD PTR [edi+3804]
	mov DWORD PTR [edi+3948], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3840]
	add eax, ebx
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, ebx
	mov DWORD PTR [edi+3896], eax
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3840], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3844], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3848], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3852], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3856], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3860], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3864], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3868], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3872], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3876], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3880], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3884], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3888], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3892], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3896], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3900], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3904], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3908], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3912], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3916], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3920], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3924], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3928], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3932], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3936], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3940], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3944], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [edi+3948], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3840]
	add eax, ebx
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [edi+3896]
	add eax, ebx
	mov DWORD PTR [edi+3896], eax
	mov ebp, DWORD PTR [esp+8]
	add ebp, edi
	mov ebx, 0
	mov eax, DWORD PTR [edi+3840]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3844]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+4], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3848]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+8], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3852]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+12], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3856]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+16], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3860]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+20], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3864]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+24], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3868]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+28], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3872]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+32], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3876]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+36], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3880]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+40], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3884]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+44], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3888]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+48], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3892]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+52], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3896]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+56], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3900]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+60], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3904]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3908]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3912]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3916]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3920]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+80], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3924]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+84], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3928]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+88], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3932]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+92], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3936]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+96], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3940]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+100], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3944]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+104], edx
	shr ebx, 16
	mov eax, DWORD PTR [edi+3948]
	add ebx, eax
	mov edx, ebx
	and edx, 65535
	mov DWORD PTR [ebp+108], edx
	shr ebx, 16
	mov ebx, DWORD PTR [edi+4080]
	mov esi, DWORD PTR [edi+4084]
	mov ebp, DWORD PTR [edi+4092]
	mov edi, DWORD PTR [edi+4088]
	ret
	.p2align 6
