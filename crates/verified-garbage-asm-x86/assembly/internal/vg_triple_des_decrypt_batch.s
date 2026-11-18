// The functions of `src/internal/vg_triple_des_decrypt_batch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_decrypt_batch:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	mov ebp, eax
	mov DWORD PTR [ebp+328], ecx
	mov DWORD PTR [ebp+332], ebx
	mov DWORD PTR [ebp+336], esi
	mov DWORD PTR [ebp+340], edi
	mov DWORD PTR [ebp+344], edx
	mov eax, DWORD PTR [ebp+528]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+536]
	mov DWORD PTR [ebp+60], eax
	mov eax, DWORD PTR [ebp+544]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+552]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+560]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+568]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+576]
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+584]
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+592]
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+600]
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+608]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+616]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+624]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+632]
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+640]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+648]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+656]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+664]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+672]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [ebp+680]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+688]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+696]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+704]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+712]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+720]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+728]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+736]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+744]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+752]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+760]
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+768]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+776]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [ebp+532]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [ebp+540]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+548]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [ebp+556]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [ebp+564]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+572]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+580]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [ebp+588]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+596]
	mov DWORD PTR [ebp+216], eax
	mov eax, DWORD PTR [ebp+604]
	mov DWORD PTR [ebp+220], eax
	mov eax, DWORD PTR [ebp+612]
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+620]
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+628]
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+636]
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+644]
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+652]
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+660]
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+668]
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+676]
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+684]
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+692]
	mov DWORD PTR [ebp+264], eax
	mov eax, DWORD PTR [ebp+700]
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [ebp+708]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+716]
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+724]
	mov DWORD PTR [ebp+280], eax
	mov eax, DWORD PTR [ebp+732]
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [ebp+740]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+748]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+756]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+764]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+772]
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+780]
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+120]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+120], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+124]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+124], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+128]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+128], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+136]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+136], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+84]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+152], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+100]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+108], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+116]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+88]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+88], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+92]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+92], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+96]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+96], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+104]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+104], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+84]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+152], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+132]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+132], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+140]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+140], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+148]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+76]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+80]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+80], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+104]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+104], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+100]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+136]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+136], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+132]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+132], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+156]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+156], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+164]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+64]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+64], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+68]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+68], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+80]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+80], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+96]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+96], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+108], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+128]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+128], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+140]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+140], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+156]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+156], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+172], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+60]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+76]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+92]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+124]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+176], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+248]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+248], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+252]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+252], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+256]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+264]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+264], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+212], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+280]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+280], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+228]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+236]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+236], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+216]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+216], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+220]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+220], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+224]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+224], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+232]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+232], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+212], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+280]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+280], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+260]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+260], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+268]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+268], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+272], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+276]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+276], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+200]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+200], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+204], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+208]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+208], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+232]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+232], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+228]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+264]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+264], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+260]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+260], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+284]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+284], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+292]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+292], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+192]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+192], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+196]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+196], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+208]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+208], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+224]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+224], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+236]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+236], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+256]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+268]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+268], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+284]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+284], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+296], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+300]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+300], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+188], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+196]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+196], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+220]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+220], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+272], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+296], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+304]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+304], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+328]
	add eax, 376
	mov DWORD PTR [ebp+320], eax
	mov eax, 8
	mov DWORD PTR [ebp+324], eax
20:
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	sub eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], eax
	xor ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], ebx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+288], ecx
	xor edx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+296], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+256], eax
	xor ebx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+272], ebx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+184], ecx
	xor edx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+168], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	xor ebx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+120], ebx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+72], ecx
	xor edx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+304], eax
	xor ebx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+264], ebx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+192], ecx
	xor edx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+248], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+240], eax
	xor ebx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+280], ebx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+136], ecx
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+80], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+224], eax
	xor ebx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+232], ebx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+152], ecx
	xor edx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+208], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+112], eax
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+200], ecx
	xor edx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+56], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+160], eax
	xor ebx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+216], ecx
	xor edx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+176], edx
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	sub eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+292], ecx
	xor edx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+300], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+260], eax
	xor ebx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+276], ebx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+188], ecx
	xor edx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+172], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+148], eax
	xor ebx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], ebx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+76], ecx
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+308], eax
	xor ebx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+268], ebx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+196], ecx
	xor edx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+252], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+244], eax
	xor ebx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+284], ebx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	xor edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+84], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+228], eax
	xor ebx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+236], ebx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+156], ecx
	xor edx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+212], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ebx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+204], ecx
	xor edx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+60], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+164], eax
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], ebx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+220], ecx
	xor edx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+180], edx
	mov eax, DWORD PTR [ebp+324]
	sub eax, 1
	mov DWORD PTR [ebp+324], eax
	jne 20b
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+56], ecx
	mov DWORD PTR [ebp+60], eax
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+88], ecx
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+120], ecx
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+152], ecx
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+184], ecx
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+216], ecx
	mov DWORD PTR [ebp+220], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+248], ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+280], ecx
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+128], ecx
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+160], ecx
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+192], ecx
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+224], ecx
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+256], ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+288], ecx
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+72], ecx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+136], ecx
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+168], ecx
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+200], ecx
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+232], ecx
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+264], ecx
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+296], ecx
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+80], ecx
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+112], ecx
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+144], ecx
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+176], ecx
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+208], ecx
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+240], ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+272], ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+304]
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+304], ecx
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+328]
	add eax, 128
	mov DWORD PTR [ebp+320], eax
	mov eax, 8
	mov DWORD PTR [ebp+324], eax
21:
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	add eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], eax
	xor ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], ebx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+288], ecx
	xor edx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+296], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+256], eax
	xor ebx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+272], ebx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+184], ecx
	xor edx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+168], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	xor ebx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+120], ebx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+72], ecx
	xor edx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+304], eax
	xor ebx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+264], ebx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+192], ecx
	xor edx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+248], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+240], eax
	xor ebx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+280], ebx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+136], ecx
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+80], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+224], eax
	xor ebx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+232], ebx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+152], ecx
	xor edx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+208], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+112], eax
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+200], ecx
	xor edx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+56], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+160], eax
	xor ebx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+216], ecx
	xor edx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+176], edx
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	add eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+292], ecx
	xor edx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+300], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+260], eax
	xor ebx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+276], ebx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+188], ecx
	xor edx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+172], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+148], eax
	xor ebx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], ebx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+76], ecx
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+308], eax
	xor ebx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+268], ebx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+196], ecx
	xor edx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+252], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+244], eax
	xor ebx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+284], ebx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	xor edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+84], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+228], eax
	xor ebx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+236], ebx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+156], ecx
	xor edx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+212], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ebx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+204], ecx
	xor edx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+60], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+164], eax
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], ebx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+220], ecx
	xor edx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+180], edx
	mov eax, DWORD PTR [ebp+324]
	sub eax, 1
	mov DWORD PTR [ebp+324], eax
	jne 21b
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+56], ecx
	mov DWORD PTR [ebp+60], eax
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+88], ecx
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+120], ecx
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+152], ecx
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+184], ecx
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+216], ecx
	mov DWORD PTR [ebp+220], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+248], ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+280], ecx
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+128], ecx
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+160], ecx
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+192], ecx
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+224], ecx
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+256], ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+288], ecx
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+72], ecx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+136], ecx
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+168], ecx
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+200], ecx
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+232], ecx
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+264], ecx
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+296], ecx
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+80], ecx
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+112], ecx
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+144], ecx
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+176], ecx
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+208], ecx
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+240], ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+272], ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+304]
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+304], ecx
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+328]
	add eax, 120
	mov DWORD PTR [ebp+320], eax
	mov eax, 8
	mov DWORD PTR [ebp+324], eax
22:
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	sub eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], eax
	xor ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], ebx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+288], ecx
	xor edx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+296], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+256], eax
	xor ebx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+272], ebx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+184], ecx
	xor edx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+168], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	xor ebx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+120], ebx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+72], ecx
	xor edx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+304], eax
	xor ebx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+264], ebx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+192], ecx
	xor edx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+248], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+240], eax
	xor ebx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+280], ebx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+136], ecx
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+80], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+224], eax
	xor ebx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+232], ebx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+152], ecx
	xor edx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+208], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+112], eax
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+200], ecx
	xor edx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+56], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+160], eax
	xor ebx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+216], ecx
	xor edx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+176], edx
	mov eax, DWORD PTR [ebp+320]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+312], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+316], ecx
	sub eax, 8
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+316]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+12]
	mov esi, ecx
	and esi, edx
	mov edi, DWORD PTR [ebp+8]
	xor edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, ebx
	xor ecx, -1
	and ecx, edi
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+32], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, eax
	xor edx, -1
	and edx, ebx
	or esi, DWORD PTR [ebp]
	xor edx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edx
	mov DWORD PTR [ebp+36], esi
	mov esi, DWORD PTR [ebp+20]
	or esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, edx
	or ecx, esi
	xor edi, -1
	and edi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	xor edx, edi
	xor esi, -1
	and esi, DWORD PTR [ebp+8]
	xor esi, edi
	mov DWORD PTR [ebp+8], edi
	mov edi, DWORD PTR [ebp+32]
	xor edi, -1
	and edi, eax
	or esi, edi
	mov edi, DWORD PTR [ebp+28]
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+28], esi
	mov esi, ebx
	xor esi, ecx
	xor edi, -1
	and edi, esi
	mov esi, edi
	xor esi, -1
	mov DWORD PTR [ebp+12], ebx
	mov ebx, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+40]
	xor esi, ebx
	or edx, DWORD PTR [ebp+16]
	xor edx, DWORD PTR [ebp+16]
	xor edx, esi
	xor edi, eax
	or edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	xor esi, edi
	mov ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+16]
	xor ebx, esi
	xor ecx, DWORD PTR [ebp+24]
	or ecx, DWORD PTR [ebp+28]
	xor ecx, edi
	or eax, esi
	xor eax, ecx
	mov esi, DWORD PTR [ebp+36]
	or esi, DWORD PTR [ebp+16]
	xor esi, eax
	mov eax, DWORD PTR [ebp+4]
	or eax, DWORD PTR [ebp+12]
	xor ecx, -1
	and ecx, eax
	and edi, DWORD PTR [ebp+36]
	xor ecx, edi
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+28]
	mov eax, ecx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, edx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	xor ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+292], ecx
	xor edx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+300], edx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, ebx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, eax
	mov esi, DWORD PTR [ebp+20]
	and esi, eax
	xor esi, DWORD PTR [ebp+4]
	mov edi, edx
	xor edi, -1
	and edi, esi
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+12]
	and edi, DWORD PTR [ebp]
	xor ebx, edx
	and ebx, ecx
	mov edx, edi
	xor edx, -1
	and edx, ebx
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+12]
	and ecx, ebx
	mov DWORD PTR [ebp+28], ebx
	mov ebx, DWORD PTR [ebp+20]
	xor ebx, -1
	xor ebx, ecx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov DWORD PTR [ebp], eax
	mov eax, edi
	xor eax, -1
	and eax, ecx
	mov DWORD PTR [ebp+32], edi
	mov edi, ebx
	xor edi, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	xor edx, edi
	xor eax, -1
	and eax, DWORD PTR [ebp+16]
	xor esi, eax
	or ebx, esi
	xor ebx, esi
	mov DWORD PTR [ebp+16], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+24]
	xor ecx, ebx
	xor eax, DWORD PTR [ebp+20]
	or edx, eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, edi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp+32]
	or ecx, eax
	mov DWORD PTR [ebp+32], eax
	mov eax, edx
	xor eax, ecx
	xor edi, DWORD PTR [ebp+28]
	xor ebx, edi
	and ecx, ebx
	and edx, DWORD PTR [ebp]
	xor ecx, edx
	mov edx, ecx
	or edx, DWORD PTR [ebp+8]
	xor edx, eax
	xor esi, -1
	and esi, ecx
	mov ecx, DWORD PTR [ebp+12]
	or ecx, DWORD PTR [ebp+32]
	xor esi, ecx
	mov ecx, DWORD PTR [ebp+4]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, esi
	mov eax, ecx
	mov ebx, edx
	mov ecx, DWORD PTR [ebp+16]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+260], eax
	xor ebx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+276], ebx
	xor ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+188], ecx
	xor edx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+172], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 31
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	add eax, eax
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+316]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp]
	mov ecx, eax
	or ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	xor edx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+20]
	xor esi, -1
	and esi, edx
	mov edi, ecx
	xor edi, esi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+16]
	xor eax, ebx
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp]
	xor esi, -1
	and esi, eax
	xor ecx, esi
	mov esi, ecx
	xor esi, -1
	and esi, edi
	mov DWORD PTR [ebp+32], esi
	mov esi, DWORD PTR [ebp]
	and esi, edi
	or esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp+20]
	xor esi, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, -1
	and eax, edi
	xor eax, esi
	and ebx, edx
	mov edx, DWORD PTR [ebp+20]
	xor edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, ecx
	xor eax, edx
	or eax, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, eax
	or edx, DWORD PTR [ebp+28]
	mov eax, edx
	xor eax, -1
	and eax, esi
	mov DWORD PTR [ebp+28], esi
	mov esi, DWORD PTR [ebp+8]
	and esi, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, esi
	xor eax, edx
	and ecx, eax
	or esi, DWORD PTR [ebp+36]
	xor ecx, -1
	and ecx, esi
	xor ecx, DWORD PTR [ebp+20]
	and ebx, DWORD PTR [ebp+4]
	xor ebx, ecx
	xor edi, -1
	mov esi, DWORD PTR [ebp+16]
	or esi, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+36]
	mov edx, DWORD PTR [ebp]
	xor edx, esi
	mov DWORD PTR [ebp], ebx
	mov ebx, DWORD PTR [ebp+32]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+28]
	or esi, edi
	xor ecx, DWORD PTR [ebp+24]
	xor esi, ecx
	or eax, DWORD PTR [ebp+4]
	xor eax, esi
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+24], ebx
	mov ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+148], eax
	xor ebx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], ebx
	xor ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+76], ecx
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 25
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 26
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 27
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 28
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 29
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 30
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, DWORD PTR [ebp+4]
	mov ecx, DWORD PTR [ebp+16]
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+4]
	xor ecx, -1
	and ecx, ebx
	mov edx, DWORD PTR [ebp+16]
	xor edx, -1
	and edx, ebx
	mov esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edi, eax
	or edi, esi
	or edi, ecx
	xor edi, ecx
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp+16]
	xor edx, edi
	and esi, edx
	or ebx, esi
	xor ebx, esi
	xor eax, edx
	xor ebx, -1
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+16]
	xor ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edx
	mov edx, DWORD PTR [ebp+4]
	or edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edx, ebx
	xor edx, -1
	and edx, eax
	xor edi, edx
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp]
	xor edx, edi
	xor edi, -1
	mov DWORD PTR [ebp+12], edx
	mov edx, DWORD PTR [ebp]
	xor edx, -1
	and edx, ecx
	xor edx, edi
	xor ecx, edi
	xor ebx, -1
	and ebx, ecx
	or esi, ebx
	xor eax, esi
	mov esi, DWORD PTR [ebp+8]
	or esi, DWORD PTR [ebp]
	xor esi, eax
	mov ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+8]
	xor ebx, eax
	mov eax, ebx
	mov ebx, esi
	mov ecx, edx
	mov edx, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+308], eax
	xor ebx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+268], ebx
	xor ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+196], ecx
	xor edx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+252], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 19
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 20
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 21
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 22
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 23
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 24
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+20]
	or eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp]
	xor ebx, -1
	and ebx, eax
	mov ecx, DWORD PTR [ebp+20]
	xor ecx, ebx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov esi, DWORD PTR [ebp+8]
	or esi, edx
	or ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+8]
	xor ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+4]
	and edi, ebx
	or edx, DWORD PTR [ebp+20]
	xor edi, edx
	xor edi, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, edi
	mov DWORD PTR [ebp], edi
	mov edi, ecx
	or edi, eax
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+4]
	and eax, edi
	mov DWORD PTR [ebp+28], esi
	mov esi, ecx
	xor esi, eax
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+8]
	and ecx, edx
	xor esi, ecx
	or edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+20]
	mov ecx, ebx
	xor ecx, edi
	mov DWORD PTR [ebp+36], edx
	mov edx, DWORD PTR [ebp+4]
	xor edx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, edx
	xor ecx, -1
	or ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, ebx
	xor edi, edx
	or edi, esi
	xor ecx, -1
	and ecx, edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+4], edi
	mov edi, DWORD PTR [ebp+24]
	and edi, ecx
	xor edx, edi
	mov edi, ebx
	and edi, DWORD PTR [ebp+36]
	or edi, edx
	xor eax, edi
	and eax, DWORD PTR [ebp+16]
	xor eax, esi
	mov esi, DWORD PTR [ebp+20]
	xor esi, DWORD PTR [ebp+12]
	xor ecx, esi
	mov esi, DWORD PTR [ebp+8]
	and esi, edx
	xor ecx, esi
	mov esi, DWORD PTR [ebp+4]
	or esi, DWORD PTR [ebp+16]
	xor esi, ecx
	xor ebx, DWORD PTR [ebp+28]
	xor ecx, -1
	and ecx, ebx
	xor edx, DWORD PTR [ebp+32]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+28]
	and edx, DWORD PTR [ebp+16]
	xor edx, ecx
	mov ebx, DWORD PTR [ebp]
	mov ecx, edx
	mov edx, esi
	xor eax, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+244], eax
	xor ebx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+284], ebx
	xor ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	xor edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+84], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 13
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 14
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 15
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 16
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 17
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 18
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+16]
	or ebx, DWORD PTR [ebp]
	and ebx, DWORD PTR [ebp+20]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	xor ecx, eax
	mov edx, ecx
	xor edx, -1
	and edx, DWORD PTR [ebp+4]
	and ecx, DWORD PTR [ebp+20]
	mov esi, DWORD PTR [ebp+16]
	xor esi, ecx
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+24], ecx
	mov ecx, esi
	or ecx, edi
	mov DWORD PTR [ebp+28], ebx
	mov ebx, eax
	xor ebx, ecx
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, ebx
	mov DWORD PTR [ebp+36], edi
	mov edi, DWORD PTR [ebp]
	xor edi, -1
	and edi, eax
	or esi, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, edi
	xor edx, esi
	mov DWORD PTR [ebp+44], edi
	mov edi, edx
	and edi, DWORD PTR [ebp+8]
	xor edi, ebx
	xor ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+48], edi
	mov edi, ecx
	xor edi, -1
	and edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+12]
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	xor ecx, -1
	and ecx, DWORD PTR [ebp+4]
	or ecx, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+16]
	or eax, DWORD PTR [ebp+36]
	xor edx, eax
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+28]
	or eax, ecx
	xor edx, eax
	or ebx, DWORD PTR [ebp+20]
	and esi, ebx
	xor esi, edi
	mov ebx, DWORD PTR [ebp+44]
	xor ebx, -1
	and ebx, esi
	mov eax, DWORD PTR [ebp+40]
	or eax, DWORD PTR [ebp+8]
	xor eax, ebx
	xor esi, DWORD PTR [ebp+32]
	xor esi, -1
	and esi, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+36]
	xor ebx, -1
	xor ebx, DWORD PTR [ebp+12]
	xor esi, ebx
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	xor esi, edx
	mov edx, DWORD PTR [ebp]
	xor edx, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+20]
	and edx, edi
	xor ebx, DWORD PTR [ebp+52]
	xor edx, ebx
	or ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+8]
	xor ecx, edx
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+48]
	mov ebx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+52], ecx
	mov ecx, esi
	mov edx, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+228], eax
	xor ebx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+236], ebx
	xor ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+156], ecx
	xor edx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+212], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 7
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 8
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 9
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 10
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 11
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 12
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+4]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, eax
	mov ecx, DWORD PTR [ebp]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+8]
	and edx, eax
	mov esi, DWORD PTR [ebp+16]
	xor esi, edx
	mov edi, ecx
	and edi, esi
	mov DWORD PTR [ebp+24], ecx
	mov ecx, DWORD PTR [ebp]
	and ecx, edx
	mov DWORD PTR [ebp+28], edx
	mov edx, DWORD PTR [ebp+12]
	xor edx, ecx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, esi
	or ecx, edx
	xor eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+36], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [ebp+40], ecx
	mov ecx, edi
	xor ecx, -1
	and ecx, DWORD PTR [ebp+20]
	xor ecx, edx
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	mov edx, esi
	or edx, ebx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+24], edx
	mov edx, eax
	xor edx, -1
	and edx, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+8], edi
	mov edi, edx
	xor edi, -1
	and edi, esi
	xor ecx, DWORD PTR [ebp+4]
	xor edi, ecx
	or eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+32]
	or edx, eax
	mov ecx, DWORD PTR [ebp+16]
	xor ecx, DWORD PTR [ebp+40]
	and ecx, edi
	xor ecx, edx
	mov DWORD PTR [ebp+40], edx
	mov edx, ecx
	and edx, DWORD PTR [ebp+20]
	xor edx, edi
	or esi, DWORD PTR [ebp+12]
	xor esi, DWORD PTR [ebp+12]
	or eax, esi
	or edi, DWORD PTR [ebp+28]
	and eax, edi
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+40]
	and ebx, DWORD PTR [ebp]
	or ebx, DWORD PTR [ebp+8]
	xor eax, ebx
	mov edi, DWORD PTR [ebp+20]
	xor edi, -1
	and edi, eax
	xor edi, DWORD PTR [ebp+24]
	and ebx, DWORD PTR [ebp+16]
	mov esi, DWORD PTR [ebp+24]
	xor esi, -1
	xor ebx, esi
	xor eax, ebx
	or ecx, DWORD PTR [ebp+20]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+44]
	mov ebx, edx
	mov edx, edi
	xor eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ebx
	xor ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+204], ecx
	xor edx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+60], edx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 1
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 2
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 3
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+8], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 4
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+12], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 5
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+16], ecx
	mov eax, DWORD PTR [ebp+312]
	shr eax, 6
	sbb ecx, ecx
	xor ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	xor eax, -1
	and eax, DWORD PTR [ebp+12]
	mov ebx, DWORD PTR [ebp+12]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+4]
	xor ebx, DWORD PTR [ebp+8]
	mov ecx, DWORD PTR [ebp+20]
	and ecx, ebx
	mov edx, eax
	xor edx, -1
	and edx, ecx
	mov esi, ebx
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	mov edi, DWORD PTR [ebp+20]
	or edi, esi
	mov DWORD PTR [ebp+24], esi
	mov esi, DWORD PTR [ebp+12]
	xor esi, -1
	and esi, DWORD PTR [ebp+16]
	xor esi, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+28], edx
	mov edx, edi
	and edx, esi
	or ecx, edx
	xor ebx, -1
	xor edx, ebx
	xor edi, -1
	and edi, DWORD PTR [ebp+12]
	xor edx, edi
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	or edi, DWORD PTR [ebp]
	xor edi, eax
	xor eax, DWORD PTR [ebp+20]
	mov ebx, DWORD PTR [ebp+4]
	and ebx, eax
	xor edx, DWORD PTR [ebp+16]
	xor ebx, edx
	mov DWORD PTR [ebp+12], edi
	mov edi, DWORD PTR [ebp+24]
	xor edi, ebx
	xor ebx, ecx
	or ebx, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+4]
	xor ebx, eax
	and ecx, DWORD PTR [ebp]
	xor ecx, ebx
	xor esi, edi
	or edx, DWORD PTR [ebp+8]
	xor edx, esi
	mov eax, DWORD PTR [ebp+20]
	xor eax, edx
	and eax, DWORD PTR [ebp]
	xor eax, edi
	or esi, DWORD PTR [ebp+8]
	xor esi, DWORD PTR [ebp+8]
	and ebx, esi
	xor edx, DWORD PTR [ebp+28]
	xor ebx, edx
	or ebx, DWORD PTR [ebp]
	xor ebx, edi
	mov DWORD PTR [ebp], ebx
	mov ebx, ecx
	mov ecx, DWORD PTR [ebp+12]
	mov edx, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+164], eax
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], ebx
	xor ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+220], ecx
	xor edx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+180], edx
	mov eax, DWORD PTR [ebp+324]
	sub eax, 1
	mov DWORD PTR [ebp+324], eax
	jne 22b
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+56], ecx
	mov DWORD PTR [ebp+60], eax
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+88], ecx
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+120], ecx
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+152], ecx
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+184], ecx
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+216], ecx
	mov DWORD PTR [ebp+220], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+248], ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+280], ecx
	mov DWORD PTR [ebp+284], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+96], ecx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+128], ecx
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+160], ecx
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+192], ecx
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+224], ecx
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+256], ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+288], ecx
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+72], ecx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+104], ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+136], ecx
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+168], ecx
	mov DWORD PTR [ebp+172], eax
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+200], ecx
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+232], ecx
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+264], ecx
	mov DWORD PTR [ebp+268], eax
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+296], ecx
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+80], ecx
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+112], ecx
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+144], ecx
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+176], ecx
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+208], ecx
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+240], ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+272], ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, DWORD PTR [ebp+304]
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+304], ecx
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+120]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+120], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+124]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+124], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+128]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+128], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+136]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+136], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+84]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+152], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+100]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+108], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+116]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+88]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+88], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+92]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+92], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+96]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+96], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+104]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+104], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+84]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+152]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+152], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+132]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+132], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+140]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+140], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+148]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+76]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+80]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+80], ecx
	mov eax, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+104]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+104], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+100]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+136]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+136], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+132]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+132], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+168]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+168], ecx
	mov eax, DWORD PTR [ebp+156]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+156], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+164]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+64]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+64], ecx
	mov eax, DWORD PTR [ebp+60]
	mov ecx, DWORD PTR [ebp+68]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+60], eax
	mov DWORD PTR [ebp+68], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+80]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+80], ecx
	mov eax, DWORD PTR [ebp+76]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+96]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+96], ecx
	mov eax, DWORD PTR [ebp+92]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+92], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+112]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+112], ecx
	mov eax, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+108], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+128]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+128], ecx
	mov eax, DWORD PTR [ebp+124]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+124], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+144]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+144], ecx
	mov eax, DWORD PTR [ebp+140]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+140], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+160]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+160], ecx
	mov eax, DWORD PTR [ebp+156]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+156], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+176]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, DWORD PTR [ebp+172]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+172], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+56]
	mov ecx, DWORD PTR [ebp+60]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], ecx
	mov eax, DWORD PTR [ebp+72]
	mov ecx, DWORD PTR [ebp+76]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+80]
	mov ecx, DWORD PTR [ebp+84]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], ecx
	mov eax, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+92]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], ecx
	mov eax, DWORD PTR [ebp+96]
	mov ecx, DWORD PTR [ebp+100]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], ecx
	mov eax, DWORD PTR [ebp+104]
	mov ecx, DWORD PTR [ebp+108]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], ecx
	mov eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+116]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], ecx
	mov eax, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+124]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], ecx
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+128], eax
	mov DWORD PTR [ebp+132], ecx
	mov eax, DWORD PTR [ebp+136]
	mov ecx, DWORD PTR [ebp+140]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+136], eax
	mov DWORD PTR [ebp+140], ecx
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], ecx
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [ebp+156]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], ecx
	mov eax, DWORD PTR [ebp+160]
	mov ecx, DWORD PTR [ebp+164]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], ecx
	mov eax, DWORD PTR [ebp+168]
	mov ecx, DWORD PTR [ebp+172]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], ecx
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+176], eax
	mov DWORD PTR [ebp+180], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+248]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+248], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+252]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+252], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+256]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+264]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+264], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+212], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+280]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+280], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+228]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+236]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+236], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 16
	xor edx, ecx
	and edx, 65535
	xor ecx, edx
	ror edx, 16
	xor eax, edx
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+216]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+216], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+220]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+220], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+224]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+224], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+232]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+232], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+212], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+280]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+280], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+260]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+260], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+268]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+268], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+272], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+276]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 8
	xor edx, ecx
	and edx, 16711935
	xor ecx, edx
	ror edx, 24
	xor eax, edx
	mov DWORD PTR [ebp+276], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+200]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+200], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+204], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+208]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+208], ecx
	mov eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+232]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+232], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+228]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+264]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+264], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+260]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+260], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+296]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+296], ecx
	mov eax, DWORD PTR [ebp+284]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+284], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+292]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 4
	xor edx, ecx
	and edx, 252645135
	xor ecx, edx
	ror edx, 28
	xor eax, edx
	mov DWORD PTR [ebp+292], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+192]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+192], ecx
	mov eax, DWORD PTR [ebp+188]
	mov ecx, DWORD PTR [ebp+196]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+188], eax
	mov DWORD PTR [ebp+196], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+208]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+208], ecx
	mov eax, DWORD PTR [ebp+204]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+224]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+224], ecx
	mov eax, DWORD PTR [ebp+220]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+220], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+240]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+240], ecx
	mov eax, DWORD PTR [ebp+236]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+236], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+256]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+252], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+272]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+272], ecx
	mov eax, DWORD PTR [ebp+268]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+268], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+288]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+288], ecx
	mov eax, DWORD PTR [ebp+284]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+284], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+304]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+296], eax
	mov DWORD PTR [ebp+304], ecx
	mov eax, DWORD PTR [ebp+300]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 2
	xor edx, ecx
	and edx, 858993459
	xor ecx, edx
	ror edx, 30
	xor eax, edx
	mov DWORD PTR [ebp+300], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+184], eax
	mov DWORD PTR [ebp+188], ecx
	mov eax, DWORD PTR [ebp+192]
	mov ecx, DWORD PTR [ebp+196]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+192], eax
	mov DWORD PTR [ebp+196], ecx
	mov eax, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], ecx
	mov eax, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+208], eax
	mov DWORD PTR [ebp+212], ecx
	mov eax, DWORD PTR [ebp+216]
	mov ecx, DWORD PTR [ebp+220]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+216], eax
	mov DWORD PTR [ebp+220], ecx
	mov eax, DWORD PTR [ebp+224]
	mov ecx, DWORD PTR [ebp+228]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], ecx
	mov eax, DWORD PTR [ebp+232]
	mov ecx, DWORD PTR [ebp+236]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], ecx
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], ecx
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], ecx
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+256], eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+264]
	mov ecx, DWORD PTR [ebp+268]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+264], eax
	mov DWORD PTR [ebp+268], ecx
	mov eax, DWORD PTR [ebp+272]
	mov ecx, DWORD PTR [ebp+276]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+272], eax
	mov DWORD PTR [ebp+276], ecx
	mov eax, DWORD PTR [ebp+280]
	mov ecx, DWORD PTR [ebp+284]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+280], eax
	mov DWORD PTR [ebp+284], ecx
	mov eax, DWORD PTR [ebp+288]
	mov ecx, DWORD PTR [ebp+292]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+288], eax
	mov DWORD PTR [ebp+292], ecx
	mov eax, DWORD PTR [ebp+296]
	mov ecx, DWORD PTR [ebp+300]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+296], eax
	mov DWORD PTR [ebp+300], ecx
	mov eax, DWORD PTR [ebp+304]
	mov ecx, DWORD PTR [ebp+308]
	mov edx, eax
	shr edx, 1
	xor edx, ecx
	and edx, 1431655765
	xor ecx, edx
	ror edx, 31
	xor eax, edx
	mov DWORD PTR [ebp+304], eax
	mov DWORD PTR [ebp+308], ecx
	mov eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+536], eax
	mov eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+544], eax
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+552], eax
	mov eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+560], eax
	mov eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+568], eax
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+576], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+584], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+592], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+600], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+608], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+616], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+624], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+632], eax
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+640], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+648], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+656], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+664], eax
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+672], eax
	mov eax, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+680], eax
	mov eax, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+688], eax
	mov eax, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+696], eax
	mov eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+704], eax
	mov eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+712], eax
	mov eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+720], eax
	mov eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+728], eax
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+736], eax
	mov eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+744], eax
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+752], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+760], eax
	mov eax, DWORD PTR [ebp+176]
	mov DWORD PTR [ebp+768], eax
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+776], eax
	mov eax, DWORD PTR [ebp+184]
	mov DWORD PTR [ebp+532], eax
	mov eax, DWORD PTR [ebp+188]
	mov DWORD PTR [ebp+540], eax
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+548], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+556], eax
	mov eax, DWORD PTR [ebp+200]
	mov DWORD PTR [ebp+564], eax
	mov eax, DWORD PTR [ebp+204]
	mov DWORD PTR [ebp+572], eax
	mov eax, DWORD PTR [ebp+208]
	mov DWORD PTR [ebp+580], eax
	mov eax, DWORD PTR [ebp+212]
	mov DWORD PTR [ebp+588], eax
	mov eax, DWORD PTR [ebp+216]
	mov DWORD PTR [ebp+596], eax
	mov eax, DWORD PTR [ebp+220]
	mov DWORD PTR [ebp+604], eax
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+612], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+620], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+628], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+636], eax
	mov eax, DWORD PTR [ebp+240]
	mov DWORD PTR [ebp+644], eax
	mov eax, DWORD PTR [ebp+244]
	mov DWORD PTR [ebp+652], eax
	mov eax, DWORD PTR [ebp+248]
	mov DWORD PTR [ebp+660], eax
	mov eax, DWORD PTR [ebp+252]
	mov DWORD PTR [ebp+668], eax
	mov eax, DWORD PTR [ebp+256]
	mov DWORD PTR [ebp+676], eax
	mov eax, DWORD PTR [ebp+260]
	mov DWORD PTR [ebp+684], eax
	mov eax, DWORD PTR [ebp+264]
	mov DWORD PTR [ebp+692], eax
	mov eax, DWORD PTR [ebp+268]
	mov DWORD PTR [ebp+700], eax
	mov eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+708], eax
	mov eax, DWORD PTR [ebp+276]
	mov DWORD PTR [ebp+716], eax
	mov eax, DWORD PTR [ebp+280]
	mov DWORD PTR [ebp+724], eax
	mov eax, DWORD PTR [ebp+284]
	mov DWORD PTR [ebp+732], eax
	mov eax, DWORD PTR [ebp+288]
	mov DWORD PTR [ebp+740], eax
	mov eax, DWORD PTR [ebp+292]
	mov DWORD PTR [ebp+748], eax
	mov eax, DWORD PTR [ebp+296]
	mov DWORD PTR [ebp+756], eax
	mov eax, DWORD PTR [ebp+300]
	mov DWORD PTR [ebp+764], eax
	mov eax, DWORD PTR [ebp+304]
	mov DWORD PTR [ebp+772], eax
	mov eax, DWORD PTR [ebp+308]
	mov DWORD PTR [ebp+780], eax
	mov ebx, DWORD PTR [ebp+332]
	mov esi, DWORD PTR [ebp+336]
	mov edi, DWORD PTR [ebp+340]
	mov ebp, DWORD PTR [ebp+344]
	ret
	.p2align 6
