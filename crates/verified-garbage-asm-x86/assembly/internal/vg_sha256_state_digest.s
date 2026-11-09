// The functions of `src/internal/vg_sha256_state_digest.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_state_digest:
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	ret
	.p2align 6
