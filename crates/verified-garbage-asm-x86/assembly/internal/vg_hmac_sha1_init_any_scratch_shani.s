// The functions of `src/internal/vg_hmac_sha1_init_any_scratch_shani.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init_any_scratch_shani:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+448], ebx
	mov DWORD PTR [eax+452], esi
	mov DWORD PTR [eax+456], edi
	mov DWORD PTR [eax+460], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+12]
	jmp 21f
20:
	mov edi, ebp
	add edi, 716
	push edi
	call {vg_sha1_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov edx, ebp
	add edx, 840
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 840
	mov ecx, 20
21:
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha1_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+448]
	mov esi, DWORD PTR [eax+452]
	mov edi, DWORD PTR [eax+456]
	mov ebp, DWORD PTR [eax+460]
	ret
	.p2align 6
