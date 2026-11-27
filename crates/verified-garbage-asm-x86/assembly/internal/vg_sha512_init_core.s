// The functions of `src/internal/vg_sha512_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -205731576
	mov DWORD PTR [eax], ecx
	mov ecx, 1779033703
	mov DWORD PTR [eax+4], ecx
	mov ecx, -2067093701
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1150833019
	mov DWORD PTR [eax+12], ecx
	mov ecx, -23791573
	mov DWORD PTR [eax+16], ecx
	mov ecx, 1013904242
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1595750129
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1521486534
	mov DWORD PTR [eax+28], ecx
	mov ecx, -1377402159
	mov DWORD PTR [eax+32], ecx
	mov ecx, 1359893119
	mov DWORD PTR [eax+36], ecx
	mov ecx, 725511199
	mov DWORD PTR [eax+40], ecx
	mov ecx, -1694144372
	mov DWORD PTR [eax+44], ecx
	mov ecx, -79577749
	mov DWORD PTR [eax+48], ecx
	mov ecx, 528734635
	mov DWORD PTR [eax+52], ecx
	mov ecx, 327033209
	mov DWORD PTR [eax+56], ecx
	mov ecx, 1541459225
	mov DWORD PTR [eax+60], ecx
	ret
	.p2align 6
