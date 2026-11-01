// The functions of `src/ed448.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+268]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	movzx eax, BYTE PTR [esp+24]
	and eax, 252
	mov BYTE PTR [esp+24], al
	movzx eax, BYTE PTR [esp+79]
	or eax, 128
	mov BYTE PTR [esp+79], al
	mov eax, 0
	mov BYTE PTR [esp+80], al
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_base}
	mov eax, 0
	mov DWORD PTR [esp+24], eax
	mov eax, 0
	mov DWORD PTR [esp+28], eax
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed448_sign_cached:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 138
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	movzx eax, BYTE PTR [esp+138]
	and eax, 252
	mov BYTE PTR [esp+138], al
	movzx eax, BYTE PTR [esp+193]
	or eax, 128
	mov BYTE PTR [esp+193], al
	mov eax, 0
	mov BYTE PTR [esp+194], al
	mov eax, DWORD PTR [esp+276]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_base}
	mov eax, DWORD PTR [esp+276]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+288]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 57
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 195
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 138
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+288]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	call {vg_ed448_scalar_mul_add}
	mov eax, 0
	mov DWORD PTR [esp+24], eax
	mov eax, 0
	mov DWORD PTR [esp+28], eax
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed448_verify:
	mov eax, DWORD PTR [esp+12]
	shr eax, 8
	cmp eax, 0
	je 20f
	mov eax, 0
	jmp 21f
20:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+268]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [esp+32], eax
	mov eax, 1164405075
	mov DWORD PTR [esp+24], eax
	mov eax, 942945380
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+284]
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	mov DWORD PTR [eax+24], edx
	mov DWORD PTR [eax+28], edx
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
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
	mov DWORD PTR [eax+192], edx
	mov DWORD PTR [eax+196], edx
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+12], eax
	mov eax, 10
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 57
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_absorb_scratch}
	mov edx, eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+16], eax
	mov DWORD PTR [esp+8], edx
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+12], eax
	mov eax, 114
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 208
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	mov eax, esp
	add eax, 160
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed448_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 160
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+284]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	call {vg_ed448_verify_equation}
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
21:
	ret
	.p2align 6
