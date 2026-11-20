// The functions of `src/internal/vg_mldsa87_verify_entry.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_verify_entry:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+20]
	add eax, 32
	mov ecx, esi
	add ecx, 136192
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 136192
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 352
	mov ecx, esi
	add ecx, 137216
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 137216
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 672
	mov ecx, esi
	add ecx, 138240
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 138240
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 992
	mov ecx, esi
	add ecx, 139264
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 139264
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1312
	mov ecx, esi
	add ecx, 140288
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 140288
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1632
	mov ecx, esi
	add ecx, 141312
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 141312
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 1952
	mov ecx, esi
	add ecx, 142336
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 142336
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 2272
	mov ecx, esi
	add ecx, 143360
	push ecx
	push eax
	call {vg_mldsa_unpack_t1}
	pop eax
	pop eax
	mov eax, esi
	add eax, 143360
	mov ecx, esi
	add ecx, 0
	push ecx
	push eax
	call {vg_mldsa_ntt}
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	add eax, 0
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 0
	mov ebx, esi
	add ebx, 0
	mov edi, esi
	add edi, 136192
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa87_verify_core}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
