// The functions of `src/internal/vg_gf448_r16_sub.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r16_sub:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	add esi, edi
	mov ebp, DWORD PTR [esp+16]
	add ebp, edi
	mov eax, DWORD PTR [esi]
	add eax, 131070
	sub eax, DWORD PTR [ebp]
	mov DWORD PTR [edi+3840], eax
	mov eax, DWORD PTR [esi+4]
	add eax, 131070
	sub eax, DWORD PTR [ebp+4]
	mov DWORD PTR [edi+3844], eax
	mov eax, DWORD PTR [esi+8]
	add eax, 131070
	sub eax, DWORD PTR [ebp+8]
	mov DWORD PTR [edi+3848], eax
	mov eax, DWORD PTR [esi+12]
	add eax, 131070
	sub eax, DWORD PTR [ebp+12]
	mov DWORD PTR [edi+3852], eax
	mov eax, DWORD PTR [esi+16]
	add eax, 131070
	sub eax, DWORD PTR [ebp+16]
	mov DWORD PTR [edi+3856], eax
	mov eax, DWORD PTR [esi+20]
	add eax, 131070
	sub eax, DWORD PTR [ebp+20]
	mov DWORD PTR [edi+3860], eax
	mov eax, DWORD PTR [esi+24]
	add eax, 131070
	sub eax, DWORD PTR [ebp+24]
	mov DWORD PTR [edi+3864], eax
	mov eax, DWORD PTR [esi+28]
	add eax, 131070
	sub eax, DWORD PTR [ebp+28]
	mov DWORD PTR [edi+3868], eax
	mov eax, DWORD PTR [esi+32]
	add eax, 131070
	sub eax, DWORD PTR [ebp+32]
	mov DWORD PTR [edi+3872], eax
	mov eax, DWORD PTR [esi+36]
	add eax, 131070
	sub eax, DWORD PTR [ebp+36]
	mov DWORD PTR [edi+3876], eax
	mov eax, DWORD PTR [esi+40]
	add eax, 131070
	sub eax, DWORD PTR [ebp+40]
	mov DWORD PTR [edi+3880], eax
	mov eax, DWORD PTR [esi+44]
	add eax, 131070
	sub eax, DWORD PTR [ebp+44]
	mov DWORD PTR [edi+3884], eax
	mov eax, DWORD PTR [esi+48]
	add eax, 131070
	sub eax, DWORD PTR [ebp+48]
	mov DWORD PTR [edi+3888], eax
	mov eax, DWORD PTR [esi+52]
	add eax, 131070
	sub eax, DWORD PTR [ebp+52]
	mov DWORD PTR [edi+3892], eax
	mov eax, DWORD PTR [esi+56]
	add eax, 131068
	sub eax, DWORD PTR [ebp+56]
	mov DWORD PTR [edi+3896], eax
	mov eax, DWORD PTR [esi+60]
	add eax, 131070
	sub eax, DWORD PTR [ebp+60]
	mov DWORD PTR [edi+3900], eax
	mov eax, DWORD PTR [esi+64]
	add eax, 131070
	sub eax, DWORD PTR [ebp+64]
	mov DWORD PTR [edi+3904], eax
	mov eax, DWORD PTR [esi+68]
	add eax, 131070
	sub eax, DWORD PTR [ebp+68]
	mov DWORD PTR [edi+3908], eax
	mov eax, DWORD PTR [esi+72]
	add eax, 131070
	sub eax, DWORD PTR [ebp+72]
	mov DWORD PTR [edi+3912], eax
	mov eax, DWORD PTR [esi+76]
	add eax, 131070
	sub eax, DWORD PTR [ebp+76]
	mov DWORD PTR [edi+3916], eax
	mov eax, DWORD PTR [esi+80]
	add eax, 131070
	sub eax, DWORD PTR [ebp+80]
	mov DWORD PTR [edi+3920], eax
	mov eax, DWORD PTR [esi+84]
	add eax, 131070
	sub eax, DWORD PTR [ebp+84]
	mov DWORD PTR [edi+3924], eax
	mov eax, DWORD PTR [esi+88]
	add eax, 131070
	sub eax, DWORD PTR [ebp+88]
	mov DWORD PTR [edi+3928], eax
	mov eax, DWORD PTR [esi+92]
	add eax, 131070
	sub eax, DWORD PTR [ebp+92]
	mov DWORD PTR [edi+3932], eax
	mov eax, DWORD PTR [esi+96]
	add eax, 131070
	sub eax, DWORD PTR [ebp+96]
	mov DWORD PTR [edi+3936], eax
	mov eax, DWORD PTR [esi+100]
	add eax, 131070
	sub eax, DWORD PTR [ebp+100]
	mov DWORD PTR [edi+3940], eax
	mov eax, DWORD PTR [esi+104]
	add eax, 131070
	sub eax, DWORD PTR [ebp+104]
	mov DWORD PTR [edi+3944], eax
	mov eax, DWORD PTR [esi+108]
	add eax, 131070
	sub eax, DWORD PTR [ebp+108]
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
