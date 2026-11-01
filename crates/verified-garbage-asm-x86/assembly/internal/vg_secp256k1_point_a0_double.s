// The functions of `src/internal/vg_secp256k1_point_a0_double.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_point_a0_double:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3584], edi
	mov edi, eax
	mov eax, 3360
	mov ecx, 3360
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3648
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3296
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3296
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3360
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3392
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3552
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3712
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3680
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3712
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3680
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3264
	mov ecx, 3648
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3264
	mov ecx, 3232
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3360
	mov ecx, 3328
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3680
	mov ecx, 3648
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3232
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [edi+3584]
	ret
	.p2align 6
