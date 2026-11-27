// The functions of `src/internal/vg_blake2b_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 20f
	mov edx, 0
	mov DWORD PTR [eax+64], edx
	mov DWORD PTR [eax+68], edx
	mov DWORD PTR [eax+72], edx
	mov DWORD PTR [eax+76], edx
	mov DWORD PTR [eax+80], edx
	mov DWORD PTR [eax+84], edx
	mov DWORD PTR [eax+88], edx
	mov DWORD PTR [eax+92], edx
	mov DWORD PTR [eax+96], edx
	mov DWORD PTR [eax+100], edx
	mov DWORD PTR [eax+104], edx
	mov DWORD PTR [eax+108], edx
	mov DWORD PTR [eax+112], edx
	mov DWORD PTR [eax+116], edx
	mov DWORD PTR [eax+120], edx
	mov DWORD PTR [eax+124], edx
	mov DWORD PTR [eax+128], edx
	mov DWORD PTR [eax+132], edx
	mov DWORD PTR [eax+136], edx
	mov DWORD PTR [eax+140], edx
	mov DWORD PTR [eax+144], edx
	mov DWORD PTR [eax+148], edx
	mov DWORD PTR [eax+152], edx
	mov DWORD PTR [eax+156], edx
	mov DWORD PTR [eax+160], edx
	mov DWORD PTR [eax+164], edx
	mov DWORD PTR [eax+168], edx
	mov DWORD PTR [eax+172], edx
	mov DWORD PTR [eax+176], edx
	mov DWORD PTR [eax+180], edx
	mov DWORD PTR [eax+184], edx
	mov DWORD PTR [eax+188], edx
	mov DWORD PTR [eax], ebx
	mov edx, DWORD PTR [esp+12]
22:
	movzx ebx, BYTE PTR [edx]
	mov BYTE PTR [eax+64], bl
	add edx, 1
	add eax, 1
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax]
	jmp 21f
20:
21:
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
	mov ecx, DWORD PTR [eax]
	xor ecx, 16842752
	mov edx, DWORD PTR [esp+16]
	ror edx, 24
	xor ecx, edx
	xor ecx, DWORD PTR [esp+8]
	mov DWORD PTR [eax], ecx
	ret
	.p2align 6
