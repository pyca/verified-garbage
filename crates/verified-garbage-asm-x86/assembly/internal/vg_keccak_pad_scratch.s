// The functions of `src/internal/vg_keccak_pad_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	add edx, ecx
	movzx ebx, BYTE PTR [edx]
	xor ebx, DWORD PTR [esp+16]
	mov BYTE PTR [edx], bl
	mov edx, ecx
	add edx, eax
	sub edx, 1
	movzx ebx, BYTE PTR [edx]
	xor ebx, 128
	mov BYTE PTR [edx], bl
	push esi
	push ecx
	call {vg_keccak_f1600}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esi+512]
	mov esi, DWORD PTR [esi+516]
	ret
	.p2align 6
