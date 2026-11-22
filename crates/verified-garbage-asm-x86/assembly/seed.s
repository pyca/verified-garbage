// The functions of `src/seed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	lea esp, [esp-840]
	mov eax, DWORD PTR [esp+844]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+848]
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 16
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax+800], ebx
	mov DWORD PTR [eax+804], esi
	mov DWORD PTR [eax+808], edi
	mov DWORD PTR [eax+812], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	bswap eax
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [ecx+4]
	bswap eax
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [ecx+8]
	bswap eax
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [ecx+12]
	bswap eax
	mov DWORD PTR [edi+556], eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -1640531527
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -1640531527
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 1013904243
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 1013904243
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 2027808486
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 2027808486
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -239350324
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -239350324
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -478700647
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -478700647
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -957401293
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -957401293
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -1914802585
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -1914802585
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 465362127
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 465362127
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 930724254
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 930724254
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 1861448508
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 1861448508
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -572070280
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -572070280
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -1144140559
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -1144140559
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, 2006686179
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, 2006686179
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -281594938
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -281594938
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -563189875
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -563189875
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+544]
	ror eax, 8
	mov ebx, DWORD PTR [edi+548]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+548], ebx
	mov eax, DWORD PTR [edi+544]
	add eax, DWORD PTR [edi+552]
	sub eax, -1126379749
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+548]
	sub eax, DWORD PTR [edi+556]
	add eax, -1126379749
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+552]
	ror eax, 24
	mov ebx, DWORD PTR [edi+556]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+556], ebx
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+124], eax
20:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+8]
	mov ebp, DWORD PTR [edi+24]
	xor ebp, DWORD PTR [edi+20]
	mov DWORD PTR [edi+32], ecx
	mov ecx, ebp
	xor ecx, DWORD PTR [edi]
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+48], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], ecx
	mov ecx, eax
	xor ecx, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+12]
	xor eax, ebp
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+64], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi]
	mov DWORD PTR [edi+68], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+72], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi]
	xor eax, ecx
	mov DWORD PTR [edi+80], eax
	mov eax, ebp
	xor eax, ecx
	mov DWORD PTR [edi+84], eax
	mov eax, ebp
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	mov DWORD PTR [edi+36], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, eax
	mov DWORD PTR [edi+96], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+72]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+68]
	xor edx, ebp
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi]
	xor edx, ebp
	mov ebp, ebx
	and ebp, eax
	mov DWORD PTR [edi+108], ebx
	mov ebx, DWORD PTR [edi+56]
	and ebx, DWORD PTR [edi+52]
	xor ebx, ebp
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+48]
	and eax, DWORD PTR [edi+80]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+32]
	and ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+84]
	xor ecx, ebp
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+36]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+104]
	xor ebp, ecx
	xor edx, eax
	xor ebx, ecx
	xor eax, DWORD PTR [edi+120]
	xor ebp, DWORD PTR [edi+76]
	xor edx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, edx
	and ebp, ebx
	mov DWORD PTR [edi+96], ebx
	mov ebx, eax
	xor ebx, ebp
	mov DWORD PTR [edi+92], ebp
	mov ebp, ecx
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+88], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	xor edx, DWORD PTR [edi+92]
	and edx, ecx
	xor edx, eax
	mov ecx, DWORD PTR [edi+96]
	xor ecx, edx
	mov DWORD PTR [edi+96], ebp
	mov ebp, ebx
	xor ebp, edx
	and eax, ebp
	xor ecx, eax
	xor ebx, eax
	and ebx, DWORD PTR [edi+96]
	xor ebx, DWORD PTR [edi+88]
	mov eax, ebx
	xor eax, ecx
	mov ebp, DWORD PTR [edi+96]
	xor ebp, edx
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+96]
	xor ebp, ebx
	mov DWORD PTR [edi+92], ebx
	mov ebx, edx
	xor ebx, ecx
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+88]
	xor ebp, eax
	mov DWORD PTR [edi+120], eax
	mov eax, ebx
	and eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], eax
	mov eax, ecx
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], eax
	mov eax, edx
	and eax, DWORD PTR [edi]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+96]
	and eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+36]
	and ebx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+96]
	and ebx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebx
	mov ebx, DWORD PTR [edi+88]
	and ebx, DWORD PTR [edi+32]
	and ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+100]
	xor ebx, ebp
	xor edx, ecx
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+80]
	xor edx, DWORD PTR [edi+44]
	xor ecx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], ebx
	mov ebx, DWORD PTR [edi+72]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+72], ebx
	mov ebx, DWORD PTR [edi+116]
	xor ebx, DWORD PTR [edi+84]
	xor ebp, eax
	mov eax, DWORD PTR [edi+108]
	xor eax, edx
	xor ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+108], ebp
	mov ebp, DWORD PTR [edi+52]
	xor ebp, DWORD PTR [edi+44]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+40]
	xor edx, ebp
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+52]
	xor eax, ebx
	xor ecx, edx
	mov DWORD PTR [edi+52], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, ebp
	xor ebx, ebp
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov ebp, DWORD PTR [edi+112]
	xor ebp, DWORD PTR [edi+48]
	xor ebp, -1
	mov DWORD PTR [edi+48], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+100]
	xor ecx, DWORD PTR [edi+52]
	xor eax, edx
	xor eax, -1
	xor ebp, DWORD PTR [edi+108]
	xor ebp, -1
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+20], ebp
	mov DWORD PTR [edi+16], edx
	mov DWORD PTR [edi+8], ecx
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+260]
	and eax, -16711936
	mov ebx, DWORD PTR [edi+264]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+268]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+272]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+276]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+280]
	and ebx, 16711935
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	and eax, -16711936
	mov ebx, DWORD PTR [edi+264]
	and ebx, 16711935
	xor eax, ebx
	xor eax, DWORD PTR [edi+272]
	mov ebx, DWORD PTR [edi+276]
	and ebx, -16711936
	xor eax, ebx
	xor eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+256]
	mov ebx, DWORD PTR [edi+260]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+264]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+268]
	and ebx, -16711936
	xor eax, ebx
	xor eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+256]
	mov ebx, DWORD PTR [edi+260]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+264]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+268]
	and ebx, -16711936
	xor eax, ebx
	xor eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+280]
	mov ebx, DWORD PTR [edi+284]
	and ebx, 16711935
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+256]
	and eax, 16711935
	mov ebx, DWORD PTR [edi+264]
	and ebx, 16711935
	xor eax, ebx
	xor eax, DWORD PTR [edi+268]
	mov ebx, DWORD PTR [edi+272]
	and ebx, 16711935
	xor eax, ebx
	xor eax, DWORD PTR [edi+280]
	mov ebx, DWORD PTR [edi+284]
	and ebx, -16711936
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+256]
	and eax, 16711935
	mov ebx, DWORD PTR [edi+260]
	and ebx, 16711935
	xor eax, ebx
	xor eax, DWORD PTR [edi+268]
	mov ebx, DWORD PTR [edi+272]
	and ebx, -16711936
	xor eax, ebx
	xor eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+256]
	and eax, 16711935
	mov ebx, DWORD PTR [edi+260]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+264]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+268]
	and ebx, -16711936
	xor eax, ebx
	mov ebx, DWORD PTR [edi+272]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+276]
	and ebx, 16711935
	xor eax, ebx
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+260]
	and eax, 16711935
	xor eax, DWORD PTR [edi+268]
	mov ebx, DWORD PTR [edi+280]
	and ebx, 16711935
	xor eax, ebx
	mov ebx, DWORD PTR [edi+284]
	and ebx, 16711935
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+288], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+292], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+296], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+300], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+304], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+308], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+312], ebx
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	and ebx, -805515268
	mov ecx, eax
	ror ecx, 8
	and ecx, 1072906227
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 16
	and ecx, -53478193
	xor ebx, ecx
	mov ecx, eax
	ror ecx, 24
	and ecx, -213912769
	xor ebx, ecx
	xor ebx, -416553173
	mov DWORD PTR [edi+316], ebx
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	mov eax, DWORD PTR [esp+8]
	add eax, 128
	cmp esi, eax
	jne 20b
	mov ebx, DWORD PTR [edi+800]
	mov esi, DWORD PTR [edi+804]
	mov ebp, DWORD PTR [edi+812]
	mov edi, DWORD PTR [edi+808]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	lea esp, [esp+840]
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

vg_seed_ecb_encrypt_aesni:
	lea esp, [esp-732]
	mov eax, DWORD PTR [esp+736]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+740]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+672], ebx
	mov DWORD PTR [eax+676], esi
	mov DWORD PTR [eax+680], edi
	mov DWORD PTR [eax+684], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+692]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+668], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
24:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+692]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
28:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+692]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
212:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+672]
	mov esi, DWORD PTR [edi+676]
	mov ebp, DWORD PTR [edi+684]
	mov edi, DWORD PTR [edi+680]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	lea esp, [esp+732]
	lea esp, [esp-736]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+736]
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

vg_seed_ecb_encrypt:
	lea esp, [esp-1108]
	mov eax, DWORD PTR [esp+1112]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1116]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1120]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov DWORD PTR [eax+816], ecx
	push ebx
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+20]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_seed_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	lea esp, [esp+1108]
	lea esp, [esp-1132]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	lea esp, [esp+1132]
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

vg_seed_ecb_decrypt_aesni:
	lea esp, [esp-732]
	mov eax, DWORD PTR [esp+736]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+740]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+672], ebx
	mov DWORD PTR [eax+676], esi
	mov DWORD PTR [eax+680], edi
	mov DWORD PTR [eax+684], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 544
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	sub esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+692]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+668], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
24:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+692]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
28:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+692]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
212:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+672]
	mov esi, DWORD PTR [edi+676]
	mov ebp, DWORD PTR [edi+684]
	mov edi, DWORD PTR [edi+680]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	lea esp, [esp+732]
	lea esp, [esp-736]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+736]
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

vg_seed_ecb_decrypt:
	lea esp, [esp-1108]
	mov eax, DWORD PTR [esp+1112]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1116]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1120]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 1
	mov DWORD PTR [eax+816], ecx
	push ebx
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+20]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_seed_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	lea esp, [esp+1108]
	lea esp, [esp-1132]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	lea esp, [esp+1132]
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
