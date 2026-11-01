// The functions of `src/ed25519.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key:
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
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	call {vg_sha512_finalize_scratch}
	mov eax, DWORD PTR [esp+192]
	and eax, -8
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+220]
	and eax, 1073741823
	or eax, 1073741824
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_base}
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

vg_ed25519_sign_cached:
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
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	call {vg_sha512_finalize_scratch}
	mov eax, DWORD PTR [esp+192]
	and eax, -8
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+220]
	and eax, 1073741823
	or eax, 1073741824
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	mov edx, 0
	add eax, 32
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_base}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	mov edx, 0
	add eax, 64
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 32
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	call {vg_ed25519_scalar_mul_add}
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

vg_ed25519_verify:
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
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	mov edx, 0
	add eax, 64
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
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
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	call {vg_ed25519_verify_equation}
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
	ret
	.p2align 6
