// The functions of `src/internal/vg_cmac_triple_des_chain_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_triple_des_chain_ssse3:
	cmp esi, 0
	je 20f
	mov DWORD PTR [edi+432], ebx
	mov DWORD PTR [edi+436], esi
	mov DWORD PTR [edi+440], ebp
	mov DWORD PTR [edi+448], edx
	mov DWORD PTR [edi+452], ebx
	mov DWORD PTR [edi+456], esi
	mov ebp, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_TRIPLE_DES_SSSE3}
	pop ecx
	mov DWORD PTR [edi], eax
	mov eax, ebp
	mov esi, edi
	mov ebp, DWORD PTR [eax]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+48], ebx
	mov ebp, DWORD PTR [eax]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+52], ebx
	mov ebp, DWORD PTR [eax+248]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+248]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+248]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+252]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+252]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+176], ebx
	mov ebp, DWORD PTR [eax+248]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+248]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+248]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+252]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+180], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+304], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+308], ebx
	mov ebp, DWORD PTR [eax+8]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+8]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+8]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+12]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+12]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+56], ebx
	mov ebp, DWORD PTR [eax+8]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+8]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+8]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+12]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+60], ebx
	mov ebp, DWORD PTR [eax+240]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+240]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+240]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+244]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+244]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+184], ebx
	mov ebp, DWORD PTR [eax+240]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+240]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+240]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+244]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+188], ebx
	mov ebp, DWORD PTR [eax+264]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+264]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+264]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+268]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+268]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+312], ebx
	mov ebp, DWORD PTR [eax+264]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+264]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+264]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+268]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+316], ebx
	mov ebp, DWORD PTR [eax+16]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+16]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+16]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+20]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+20]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+64], ebx
	mov ebp, DWORD PTR [eax+16]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+16]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+16]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+20]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+68], ebx
	mov ebp, DWORD PTR [eax+232]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+232]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+232]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+236]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+236]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+192], ebx
	mov ebp, DWORD PTR [eax+232]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+232]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+232]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+236]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+196], ebx
	mov ebp, DWORD PTR [eax+272]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+272]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+272]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+276]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+276]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+320], ebx
	mov ebp, DWORD PTR [eax+272]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+272]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+272]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+276]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+324], ebx
	mov ebp, DWORD PTR [eax+24]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+24]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+24]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+28]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+28]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+72], ebx
	mov ebp, DWORD PTR [eax+24]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+24]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+24]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+28]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+76], ebx
	mov ebp, DWORD PTR [eax+224]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+224]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+224]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+228]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+228]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+200], ebx
	mov ebp, DWORD PTR [eax+224]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+224]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+224]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+228]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+204], ebx
	mov ebp, DWORD PTR [eax+280]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+280]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+280]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+284]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+284]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+328], ebx
	mov ebp, DWORD PTR [eax+280]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+280]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+280]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+284]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+332], ebx
	mov ebp, DWORD PTR [eax+32]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+32]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+32]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+36]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+36]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+80], ebx
	mov ebp, DWORD PTR [eax+32]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+32]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+32]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+36]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+84], ebx
	mov ebp, DWORD PTR [eax+216]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+216]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+216]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+220]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+220]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+208], ebx
	mov ebp, DWORD PTR [eax+216]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+216]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+216]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+220]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+212], ebx
	mov ebp, DWORD PTR [eax+288]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+288]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+288]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+292]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+292]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+336], ebx
	mov ebp, DWORD PTR [eax+288]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+288]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+288]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+292]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+340], ebx
	mov ebp, DWORD PTR [eax+40]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+40]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+40]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+44]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+44]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+88], ebx
	mov ebp, DWORD PTR [eax+40]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+40]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+40]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+44]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+92], ebx
	mov ebp, DWORD PTR [eax+208]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+208]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+208]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+212]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+212]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+216], ebx
	mov ebp, DWORD PTR [eax+208]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+208]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+208]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+212]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+220], ebx
	mov ebp, DWORD PTR [eax+296]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+296]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+296]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+300]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+300]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+344], ebx
	mov ebp, DWORD PTR [eax+296]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+296]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+296]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+300]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+348], ebx
	mov ebp, DWORD PTR [eax+48]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+48]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+48]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+52]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+52]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+96], ebx
	mov ebp, DWORD PTR [eax+48]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+48]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+48]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+52]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+100], ebx
	mov ebp, DWORD PTR [eax+200]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+200]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+200]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+204]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+204]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+224], ebx
	mov ebp, DWORD PTR [eax+200]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+200]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+200]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+204]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+228], ebx
	mov ebp, DWORD PTR [eax+304]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+304]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+304]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+308]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+308]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+352], ebx
	mov ebp, DWORD PTR [eax+304]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+304]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+304]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+308]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+356], ebx
	mov ebp, DWORD PTR [eax+56]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+56]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+56]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+60]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+60]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+104], ebx
	mov ebp, DWORD PTR [eax+56]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+56]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+56]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+60]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+108], ebx
	mov ebp, DWORD PTR [eax+192]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+192]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+192]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+196]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+196]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+232], ebx
	mov ebp, DWORD PTR [eax+192]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+192]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+192]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+196]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+236], ebx
	mov ebp, DWORD PTR [eax+312]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+312]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+312]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+316]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+316]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+360], ebx
	mov ebp, DWORD PTR [eax+312]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+312]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+312]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+316]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+364], ebx
	mov ebp, DWORD PTR [eax+64]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+64]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+64]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+68]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+68]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+112], ebx
	mov ebp, DWORD PTR [eax+64]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+64]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+64]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+68]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+116], ebx
	mov ebp, DWORD PTR [eax+184]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+184]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+184]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+188]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+188]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+240], ebx
	mov ebp, DWORD PTR [eax+184]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+184]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+184]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+188]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+244], ebx
	mov ebp, DWORD PTR [eax+320]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+320]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+320]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+324]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+324]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+368], ebx
	mov ebp, DWORD PTR [eax+320]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+320]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+320]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+324]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+372], ebx
	mov ebp, DWORD PTR [eax+72]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+72]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+72]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+76]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+76]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+120], ebx
	mov ebp, DWORD PTR [eax+72]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+72]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+72]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+76]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+124], ebx
	mov ebp, DWORD PTR [eax+176]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+176]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+176]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+180]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+180]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+248], ebx
	mov ebp, DWORD PTR [eax+176]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+176]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+176]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+180]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+252], ebx
	mov ebp, DWORD PTR [eax+328]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+328]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+328]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+332]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+332]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+376], ebx
	mov ebp, DWORD PTR [eax+328]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+328]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+328]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+332]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+380], ebx
	mov ebp, DWORD PTR [eax+80]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+80]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+80]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+84]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+84]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+128], ebx
	mov ebp, DWORD PTR [eax+80]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+80]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+80]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+84]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+132], ebx
	mov ebp, DWORD PTR [eax+168]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+168]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+168]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+172]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+172]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+256], ebx
	mov ebp, DWORD PTR [eax+168]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+168]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+168]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+172]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+260], ebx
	mov ebp, DWORD PTR [eax+336]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+336]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+336]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+340]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+340]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+384], ebx
	mov ebp, DWORD PTR [eax+336]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+336]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+336]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+340]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+388], ebx
	mov ebp, DWORD PTR [eax+88]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+88]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+88]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+92]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+92]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+136], ebx
	mov ebp, DWORD PTR [eax+88]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+88]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+88]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+92]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+140], ebx
	mov ebp, DWORD PTR [eax+160]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+160]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+160]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+164]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+164]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+264], ebx
	mov ebp, DWORD PTR [eax+160]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+160]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+160]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+164]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+268], ebx
	mov ebp, DWORD PTR [eax+344]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+344]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+344]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+348]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+348]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+392], ebx
	mov ebp, DWORD PTR [eax+344]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+344]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+344]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+348]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+396], ebx
	mov ebp, DWORD PTR [eax+96]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+96]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+96]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+100]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+100]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+144], ebx
	mov ebp, DWORD PTR [eax+96]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+96]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+96]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+100]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+148], ebx
	mov ebp, DWORD PTR [eax+152]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+152]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+152]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+156]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+156]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+272], ebx
	mov ebp, DWORD PTR [eax+152]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+152]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+152]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+156]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+276], ebx
	mov ebp, DWORD PTR [eax+352]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+352]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+352]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+356]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+356]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+400], ebx
	mov ebp, DWORD PTR [eax+352]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+352]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+352]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+356]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+404], ebx
	mov ebp, DWORD PTR [eax+104]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+104]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+104]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+108]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+108]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+152], ebx
	mov ebp, DWORD PTR [eax+104]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+104]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+104]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+108]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+156], ebx
	mov ebp, DWORD PTR [eax+144]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+144]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+144]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+148]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+148]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+280], ebx
	mov ebp, DWORD PTR [eax+144]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+144]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+144]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+148]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+284], ebx
	mov ebp, DWORD PTR [eax+360]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+360]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+360]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+364]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+364]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+408], ebx
	mov ebp, DWORD PTR [eax+360]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+360]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+360]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+364]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+412], ebx
	mov ebp, DWORD PTR [eax+112]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+112]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+112]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+116]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+116]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+160], ebx
	mov ebp, DWORD PTR [eax+112]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+112]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+112]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+116]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+164], ebx
	mov ebp, DWORD PTR [eax+136]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+136]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+136]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+140]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+140]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+288], ebx
	mov ebp, DWORD PTR [eax+136]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+136]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+136]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+140]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+292], ebx
	mov ebp, DWORD PTR [eax+368]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+368]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+368]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+372]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+372]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+416], ebx
	mov ebp, DWORD PTR [eax+368]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+368]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+368]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+372]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+420], ebx
	mov ebp, DWORD PTR [eax+120]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+120]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+120]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+124]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+124]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+168], ebx
	mov ebp, DWORD PTR [eax+120]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+120]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+120]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+124]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+172], ebx
	mov ebp, DWORD PTR [eax+128]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+128]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+128]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+132]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+132]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+296], ebx
	mov ebp, DWORD PTR [eax+128]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+128]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+128]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+132]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+300], ebx
	mov ebp, DWORD PTR [eax+376]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+376]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+376]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+380]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+380]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+424], ebx
	mov ebp, DWORD PTR [eax+376]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+376]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+376]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+380]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+428], ebx
22:
	mov ecx, DWORD PTR [edi+448]
	mov esi, DWORD PTR [edi+452]
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [esi]
	xor edx, DWORD PTR [esi+4]
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], edx
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+12]
	bswap esi
	bswap ecx
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	ror esi, 1
	ror ecx, 1
	movd xmm0, esi
	movdqu XMMWORD PTR [edi+32], xmm0
	movd xmm7, ecx
	mov ebp, edi
	add ebp, 48
	mov edx, 3
23:
	mov ecx, 8
24:
	movdqu XMMWORD PTR [edi+16], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+32]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [edi+32], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp+8]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	add ebp, 16
	sub ecx, 1
	jne 24b
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+32], xmm7
	movdqa xmm7, xmm0
	sub edx, 1
	jne 23b
	movdqu XMMWORD PTR [edi+16], xmm7
	mov esi, DWORD PTR [edi+32]
	mov ecx, DWORD PTR [edi+16]
	ror esi, 31
	ror ecx, 31
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	bswap esi
	bswap ecx
	mov DWORD PTR [edi+8], esi
	mov DWORD PTR [edi+12], ecx
	mov eax, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+448]
	mov esi, DWORD PTR [edi+452]
	mov ebp, DWORD PTR [edi+456]
	mov ebx, DWORD PTR [edi+440]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add esi, 8
	mov DWORD PTR [edi+448], ecx
	mov DWORD PTR [edi+452], esi
	mov DWORD PTR [edi+440], ebx
	sub ebp, 1
	mov DWORD PTR [edi+456], ebp
	jne 22b
	mov ebx, DWORD PTR [edi+432]
	mov esi, DWORD PTR [edi+436]
	mov ebp, DWORD PTR [edi+440]
	jmp 21f
20:
21:
	ret
	.p2align 6
