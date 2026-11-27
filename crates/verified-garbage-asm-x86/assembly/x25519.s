// The functions of `src/x25519.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519_exchange:
	lea esp, [esp-16]
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+12], eax
	call {vg_x25519}
	lea esp, [esp+16]
	mov edx, DWORD PTR [esp+4]
	mov ecx, 0
	movzx eax, BYTE PTR [edx]
	or ecx, eax
	movzx eax, BYTE PTR [edx+1]
	or ecx, eax
	movzx eax, BYTE PTR [edx+2]
	or ecx, eax
	movzx eax, BYTE PTR [edx+3]
	or ecx, eax
	movzx eax, BYTE PTR [edx+4]
	or ecx, eax
	movzx eax, BYTE PTR [edx+5]
	or ecx, eax
	movzx eax, BYTE PTR [edx+6]
	or ecx, eax
	movzx eax, BYTE PTR [edx+7]
	or ecx, eax
	movzx eax, BYTE PTR [edx+8]
	or ecx, eax
	movzx eax, BYTE PTR [edx+9]
	or ecx, eax
	movzx eax, BYTE PTR [edx+10]
	or ecx, eax
	movzx eax, BYTE PTR [edx+11]
	or ecx, eax
	movzx eax, BYTE PTR [edx+12]
	or ecx, eax
	movzx eax, BYTE PTR [edx+13]
	or ecx, eax
	movzx eax, BYTE PTR [edx+14]
	or ecx, eax
	movzx eax, BYTE PTR [edx+15]
	or ecx, eax
	movzx eax, BYTE PTR [edx+16]
	or ecx, eax
	movzx eax, BYTE PTR [edx+17]
	or ecx, eax
	movzx eax, BYTE PTR [edx+18]
	or ecx, eax
	movzx eax, BYTE PTR [edx+19]
	or ecx, eax
	movzx eax, BYTE PTR [edx+20]
	or ecx, eax
	movzx eax, BYTE PTR [edx+21]
	or ecx, eax
	movzx eax, BYTE PTR [edx+22]
	or ecx, eax
	movzx eax, BYTE PTR [edx+23]
	or ecx, eax
	movzx eax, BYTE PTR [edx+24]
	or ecx, eax
	movzx eax, BYTE PTR [edx+25]
	or ecx, eax
	movzx eax, BYTE PTR [edx+26]
	or ecx, eax
	movzx eax, BYTE PTR [edx+27]
	or ecx, eax
	movzx eax, BYTE PTR [edx+28]
	or ecx, eax
	movzx eax, BYTE PTR [edx+29]
	or ecx, eax
	movzx eax, BYTE PTR [edx+30]
	or ecx, eax
	movzx eax, BYTE PTR [edx+31]
	or ecx, eax
	sub ecx, 1
	shr ecx, 31
	xor ecx, 1
	mov eax, ecx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-28]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+28]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_x25519_base:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_ED25519_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+12]
	mov DWORD PTR [edx+1160], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov edx, edi
	add edx, 7168
	mov ecx, 32
20:
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 1
	and eax, 1
	mov BYTE PTR [edx], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 2
	and eax, 1
	mov BYTE PTR [edx+1], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 3
	and eax, 1
	mov BYTE PTR [edx+2], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 4
	and eax, 1
	mov BYTE PTR [edx+3], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 5
	and eax, 1
	mov BYTE PTR [edx+4], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 6
	and eax, 1
	mov BYTE PTR [edx+5], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 7
	and eax, 1
	mov BYTE PTR [edx+6], al
	movzx eax, BYTE PTR [esi]
	add eax, eax
	shr eax, 8
	and eax, 1
	mov BYTE PTR [edx+7], al
	add esi, 1
	add edx, 8
	sub ecx, 1
	jne 20b
	mov eax, 0
	mov BYTE PTR [edi+7168], al
	mov eax, 0
	mov BYTE PTR [edi+7169], al
	mov eax, 0
	mov BYTE PTR [edi+7170], al
	mov eax, 0
	mov BYTE PTR [edi+7423], al
	mov eax, 1
	mov BYTE PTR [edi+7422], al
	mov eax, 324630691
	mov DWORD PTR [edi+576], eax
	mov eax, 1978355146
	mov DWORD PTR [edi+580], eax
	mov eax, 1094834347
	mov DWORD PTR [edi+584], eax
	mov eax, 7342669
	mov DWORD PTR [edi+588], eax
	mov eax, 2004478104
	mov DWORD PTR [edi+592], eax
	mov eax, -1933098887
	mov DWORD PTR [edi+596], eax
	mov eax, 728759923
	mov DWORD PTR [edi+600], eax
	mov eax, 1375956206
	mov DWORD PTR [edi+604], eax
	call {vg_ed25519_comb_main}
	mov esi, 4
21:
	push edi
	call {vg_ed25519_r32_double}
	pop eax
	sub esi, 1
	jne 21b
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+316], eax
	push edi
	call {vg_ed25519_r32_point_add}
	pop eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+128]
	adc eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+132]
	adc eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+136]
	adc eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+140]
	adc eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+144]
	adc eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+148]
	adc eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+152]
	adc eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+156]
	adc eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+92], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	adc eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	adc eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	adc eax, 0
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	adc eax, 0
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	adc eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	adc eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	adc eax, 0
	mov DWORD PTR [edi+92], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+128]
	sbb eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+132]
	sbb eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+136]
	sbb eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+140]
	sbb eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+144]
	sbb eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+148]
	sbb eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+152]
	sbb eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+156]
	sbb eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+156], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+128]
	sbb eax, ecx
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+132]
	sbb eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+136]
	sbb eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+140]
	sbb eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+144]
	sbb eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+148]
	sbb eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+152]
	sbb eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+156]
	sbb eax, 0
	mov DWORD PTR [edi+156], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+128]
	sbb eax, ecx
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+700], eax
	mov eax, 1
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+700], eax
	mov eax, 1
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+700], eax
	mov eax, 1
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+700], eax
	mov eax, 1
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+700], eax
	mov eax, 5
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+700], eax
	mov eax, 10
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, 20
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, 10
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+700], eax
	mov eax, 50
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, 100
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, 50
	call {vg_gf25519_r32_sqn}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+732], eax
	call {vg_gf25519_r32_mul}
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+572], eax
	mov esi, 5
22:
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+544], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+548], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+552], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+556], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+560], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+564], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+568], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+572], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+548]
	adc eax, 0
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+552]
	adc eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+556]
	adc eax, 0
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+560]
	adc eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+564]
	adc eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+568]
	adc eax, 0
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	adc eax, 0
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	sub esi, 1
	jne 22b
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+544], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+548], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+552], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+556], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+560], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+564], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+568], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+572], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+548]
	adc eax, 0
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+552]
	adc eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+556]
	adc eax, 0
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+560]
	adc eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+564]
	adc eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+568]
	adc eax, 0
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	adc eax, 0
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	adc eax, ecx
	mov DWORD PTR [edi+544], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+920], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+924], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 38
	mov eax, DWORD PTR [edi+896]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+864]
	adc edx, 0
	mov DWORD PTR [edi+64], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+68], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+72], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+76], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+80], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+84], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+88], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+92], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	adc eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	adc eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	adc eax, 0
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	adc eax, 0
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	adc eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	adc eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	adc eax, 0
	mov DWORD PTR [edi+92], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+64]
	adc eax, ecx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+92]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	and eax, 2147483647
	mov DWORD PTR [edi+92], eax
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+892]
	shr eax, 31
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+892]
	and eax, 2147483647
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+92], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [esi+28], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-8]
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	lea esp, [esp+8]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
