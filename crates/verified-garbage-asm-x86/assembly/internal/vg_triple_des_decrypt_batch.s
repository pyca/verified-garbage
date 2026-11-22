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
	mov ebx, DWORD PTR [ebp+332]
	mov esi, DWORD PTR [ebp+336]
	mov edi, DWORD PTR [ebp+340]
	call {vg_triple_des_pass_backward}
	mov eax, DWORD PTR [ebp+328]
	add eax, 128
	mov DWORD PTR [ebp+320], eax
	mov eax, 8
	mov DWORD PTR [ebp+324], eax
	mov ebx, DWORD PTR [ebp+332]
	mov esi, DWORD PTR [ebp+336]
	mov edi, DWORD PTR [ebp+340]
	call {vg_triple_des_pass_forward}
	mov eax, DWORD PTR [ebp+328]
	add eax, 120
	mov DWORD PTR [ebp+320], eax
	mov eax, 8
	mov DWORD PTR [ebp+324], eax
	mov ebx, DWORD PTR [ebp+332]
	mov esi, DWORD PTR [ebp+336]
	mov edi, DWORD PTR [ebp+340]
	call {vg_triple_des_pass_backward}
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
