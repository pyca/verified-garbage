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
	mov ecx, 0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	lea esp, [esp+840]
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
	push ebx
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+20]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_seed_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop ebx
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	lea esp, [esp+1108]
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
	push ebx
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+20]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_seed_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop ebx
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	lea esp, [esp+1108]
	ret
	.p2align 6

vg_seed_encrypt_blocks:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+800], ebx
	mov DWORD PTR [eax+804], esi
	mov DWORD PTR [eax+808], edi
	mov DWORD PTR [eax+812], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [ecx+32]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [ecx+36]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [ecx+40]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [ecx+44]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [ecx+48]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [ecx+52]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [ecx+56]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [ecx+60]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [ecx+64]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [ecx+68]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [ecx+72]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [ecx+76]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [ecx+80]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [ecx+84]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [ecx+88]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [ecx+92]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [ecx+96]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [ecx+100]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [ecx+104]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [ecx+108]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [ecx+112]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [ecx+116]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [ecx+120]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [ecx+124]
	mov DWORD PTR [edi+796], eax
	mov ebx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	test edx, edx
	je 20f
22:
	mov ecx, edx
	cmp edx, 8
	jb 23f
	mov ecx, 8
	jmp 24f
23:
24:
	cmp ecx, 1
	jb 25f
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+556], eax
	jmp 26f
25:
26:
	cmp ecx, 2
	jb 27f
	mov eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+572], eax
	jmp 28f
27:
28:
	cmp ecx, 3
	jb 29f
	mov eax, DWORD PTR [ebx+32]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [ebx+36]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [ebx+40]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [ebx+44]
	mov DWORD PTR [edi+588], eax
	jmp 210f
29:
210:
	cmp ecx, 4
	jb 211f
	mov eax, DWORD PTR [ebx+48]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [ebx+52]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [ebx+56]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [ebx+60]
	mov DWORD PTR [edi+604], eax
	jmp 212f
211:
212:
	cmp ecx, 5
	jb 213f
	mov eax, DWORD PTR [ebx+64]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [ebx+68]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [ebx+72]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [ebx+76]
	mov DWORD PTR [edi+620], eax
	jmp 214f
213:
214:
	cmp ecx, 6
	jb 215f
	mov eax, DWORD PTR [ebx+80]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [ebx+84]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [ebx+88]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [ebx+92]
	mov DWORD PTR [edi+636], eax
	jmp 216f
215:
216:
	cmp ecx, 7
	jb 217f
	mov eax, DWORD PTR [ebx+96]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [ebx+100]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [ebx+104]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [ebx+108]
	mov DWORD PTR [edi+652], eax
	jmp 218f
217:
218:
	cmp ecx, 8
	jb 219f
	mov eax, DWORD PTR [ebx+112]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [ebx+116]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [ebx+120]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [ebx+124]
	mov DWORD PTR [edi+668], eax
	jmp 220f
219:
220:
	mov DWORD PTR [edi+804], esi
	mov DWORD PTR [edi+812], ebp
	mov DWORD PTR [edi+816], ebx
	mov DWORD PTR [edi+820], edx
	mov eax, DWORD PTR [edi+544]
	bswap eax
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+548]
	bswap eax
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+552]
	bswap eax
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+556]
	bswap eax
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+560]
	bswap eax
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+564]
	bswap eax
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+568]
	bswap eax
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+572]
	bswap eax
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+576]
	bswap eax
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+580]
	bswap eax
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+584]
	bswap eax
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+588]
	bswap eax
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+592]
	bswap eax
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+596]
	bswap eax
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+600]
	bswap eax
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+604]
	bswap eax
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+608]
	bswap eax
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+612]
	bswap eax
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+616]
	bswap eax
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+620]
	bswap eax
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+624]
	bswap eax
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+628]
	bswap eax
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+632]
	bswap eax
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+636]
	bswap eax
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+640]
	bswap eax
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+644]
	bswap eax
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+648]
	bswap eax
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+652]
	bswap eax
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+656]
	bswap eax
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+660]
	bswap eax
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+664]
	bswap eax
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [edi+668]
	bswap eax
	mov DWORD PTR [edi+540], eax
	mov esi, edi
	add esi, 672
221:
	mov ecx, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+480]
	xor eax, ecx
	mov DWORD PTR [edi+320], eax
	xor eax, DWORD PTR [edi+512]
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+484]
	xor eax, ecx
	mov DWORD PTR [edi+324], eax
	xor eax, DWORD PTR [edi+516]
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+488]
	xor eax, ecx
	mov DWORD PTR [edi+328], eax
	xor eax, DWORD PTR [edi+520]
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+492]
	xor eax, ecx
	mov DWORD PTR [edi+332], eax
	xor eax, DWORD PTR [edi+524]
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+496]
	xor eax, ecx
	mov DWORD PTR [edi+336], eax
	xor eax, DWORD PTR [edi+528]
	xor eax, edx
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+500]
	xor eax, ecx
	mov DWORD PTR [edi+340], eax
	xor eax, DWORD PTR [edi+532]
	xor eax, edx
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+504]
	xor eax, ecx
	mov DWORD PTR [edi+344], eax
	xor eax, DWORD PTR [edi+536]
	xor eax, edx
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+508]
	xor eax, ecx
	mov DWORD PTR [edi+348], eax
	xor eax, DWORD PTR [edi+540]
	xor eax, edx
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
	mov DWORD PTR [edi+352], eax
	add eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+356], eax
	add eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+360], eax
	add eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+364], eax
	add eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+368], eax
	add eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+372], eax
	add eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+376], eax
	add eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+380], eax
	add eax, DWORD PTR [edi+348]
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
	mov DWORD PTR [edi+384], eax
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+388], eax
	add eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+392], eax
	add eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+396], eax
	add eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+400], eax
	add eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+404], eax
	add eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+408], eax
	add eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+412], eax
	add eax, DWORD PTR [edi+380]
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
	mov ebx, DWORD PTR [edi+448]
	xor ebx, eax
	mov DWORD PTR [edi+448], ebx
	add eax, DWORD PTR [edi+384]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+452]
	xor ebx, eax
	mov DWORD PTR [edi+452], ebx
	add eax, DWORD PTR [edi+388]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+456]
	xor ebx, eax
	mov DWORD PTR [edi+456], ebx
	add eax, DWORD PTR [edi+392]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+460]
	xor ebx, eax
	mov DWORD PTR [edi+460], ebx
	add eax, DWORD PTR [edi+396]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+464]
	xor ebx, eax
	mov DWORD PTR [edi+464], ebx
	add eax, DWORD PTR [edi+400]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+468]
	xor ebx, eax
	mov DWORD PTR [edi+468], ebx
	add eax, DWORD PTR [edi+404]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+472]
	xor ebx, eax
	mov DWORD PTR [edi+472], ebx
	add eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+476]
	xor ebx, eax
	mov DWORD PTR [edi+476], ebx
	add eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+444], eax
	add esi, 8
	mov ecx, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+416]
	xor eax, ecx
	mov DWORD PTR [edi+320], eax
	xor eax, DWORD PTR [edi+448]
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, ecx
	mov DWORD PTR [edi+324], eax
	xor eax, DWORD PTR [edi+452]
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, ecx
	mov DWORD PTR [edi+328], eax
	xor eax, DWORD PTR [edi+456]
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, ecx
	mov DWORD PTR [edi+332], eax
	xor eax, DWORD PTR [edi+460]
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, ecx
	mov DWORD PTR [edi+336], eax
	xor eax, DWORD PTR [edi+464]
	xor eax, edx
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, ecx
	mov DWORD PTR [edi+340], eax
	xor eax, DWORD PTR [edi+468]
	xor eax, edx
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, ecx
	mov DWORD PTR [edi+344], eax
	xor eax, DWORD PTR [edi+472]
	xor eax, edx
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, ecx
	mov DWORD PTR [edi+348], eax
	xor eax, DWORD PTR [edi+476]
	xor eax, edx
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
	mov DWORD PTR [edi+352], eax
	add eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+356], eax
	add eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+360], eax
	add eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+364], eax
	add eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+368], eax
	add eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+372], eax
	add eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+376], eax
	add eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+380], eax
	add eax, DWORD PTR [edi+348]
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
	mov DWORD PTR [edi+384], eax
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+388], eax
	add eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+392], eax
	add eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+396], eax
	add eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+400], eax
	add eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+404], eax
	add eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+408], eax
	add eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+412], eax
	add eax, DWORD PTR [edi+380]
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
	mov ebx, DWORD PTR [edi+512]
	xor ebx, eax
	mov DWORD PTR [edi+512], ebx
	add eax, DWORD PTR [edi+384]
	xor eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+516]
	xor ebx, eax
	mov DWORD PTR [edi+516], ebx
	add eax, DWORD PTR [edi+388]
	xor eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+520]
	xor ebx, eax
	mov DWORD PTR [edi+520], ebx
	add eax, DWORD PTR [edi+392]
	xor eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+524]
	xor ebx, eax
	mov DWORD PTR [edi+524], ebx
	add eax, DWORD PTR [edi+396]
	xor eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+528]
	xor ebx, eax
	mov DWORD PTR [edi+528], ebx
	add eax, DWORD PTR [edi+400]
	xor eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+532]
	xor ebx, eax
	mov DWORD PTR [edi+532], ebx
	add eax, DWORD PTR [edi+404]
	xor eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+536]
	xor ebx, eax
	mov DWORD PTR [edi+536], ebx
	add eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+540]
	xor ebx, eax
	mov DWORD PTR [edi+540], ebx
	add eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+508], eax
	add esi, 8
	mov eax, esi
	sub eax, edi
	cmp eax, 800
	jne 221b
	mov eax, DWORD PTR [edi+480]
	bswap eax
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+512]
	bswap eax
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+416]
	bswap eax
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+448]
	bswap eax
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+484]
	bswap eax
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+516]
	bswap eax
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+420]
	bswap eax
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+452]
	bswap eax
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+488]
	bswap eax
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+520]
	bswap eax
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+424]
	bswap eax
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+456]
	bswap eax
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+492]
	bswap eax
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+524]
	bswap eax
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+428]
	bswap eax
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+460]
	bswap eax
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+496]
	bswap eax
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+528]
	bswap eax
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+432]
	bswap eax
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+464]
	bswap eax
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+500]
	bswap eax
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+532]
	bswap eax
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+436]
	bswap eax
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+468]
	bswap eax
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+504]
	bswap eax
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+536]
	bswap eax
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+440]
	bswap eax
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+472]
	bswap eax
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+508]
	bswap eax
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+540]
	bswap eax
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+444]
	bswap eax
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+476]
	bswap eax
	mov DWORD PTR [edi+668], eax
	mov esi, DWORD PTR [edi+804]
	mov ebp, DWORD PTR [edi+812]
	mov ebx, DWORD PTR [edi+816]
	mov edx, DWORD PTR [edi+820]
	mov ecx, edx
	cmp edx, 8
	jb 222f
	mov ecx, 8
	jmp 223f
222:
223:
	cmp ecx, 1
	jb 224f
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [ebx+12], eax
	jmp 225f
224:
225:
	cmp ecx, 2
	jb 226f
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [ebx+24], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [ebx+28], eax
	jmp 227f
226:
227:
	cmp ecx, 3
	jb 228f
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [ebx+32], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [ebx+40], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [ebx+44], eax
	jmp 229f
228:
229:
	cmp ecx, 4
	jb 230f
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [ebx+48], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [ebx+52], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [ebx+56], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [ebx+60], eax
	jmp 231f
230:
231:
	cmp ecx, 5
	jb 232f
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [ebx+64], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [ebx+68], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [ebx+72], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [ebx+76], eax
	jmp 233f
232:
233:
	cmp ecx, 6
	jb 234f
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [ebx+80], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [ebx+84], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [ebx+88], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [ebx+92], eax
	jmp 235f
234:
235:
	cmp ecx, 7
	jb 236f
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [ebx+96], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [ebx+100], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [ebx+104], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [ebx+108], eax
	jmp 237f
236:
237:
	cmp ecx, 8
	jb 238f
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [ebx+112], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [ebx+116], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [ebx+120], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [ebx+124], eax
	jmp 239f
238:
239:
	add ebx, 128
	sub edx, ecx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [edi+800]
	mov edi, DWORD PTR [edi+808]
	ret
	.p2align 6

vg_seed_decrypt_blocks:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+800], ebx
	mov DWORD PTR [eax+804], esi
	mov DWORD PTR [eax+808], edi
	mov DWORD PTR [eax+812], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx+120]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [ecx+124]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [ecx+112]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [ecx+116]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [ecx+104]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [ecx+108]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [ecx+96]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [ecx+100]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [ecx+88]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [ecx+92]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [ecx+80]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [ecx+84]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [ecx+72]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [ecx+76]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [ecx+64]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [ecx+68]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [ecx+56]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [ecx+60]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [ecx+48]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [ecx+52]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [ecx+40]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [ecx+44]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [ecx+32]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [ecx+36]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+796], eax
	mov ebx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	test edx, edx
	je 20f
22:
	mov ecx, edx
	cmp edx, 8
	jb 23f
	mov ecx, 8
	jmp 24f
23:
24:
	cmp ecx, 1
	jb 25f
	mov eax, DWORD PTR [ebx]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [ebx+4]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [ebx+8]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+556], eax
	jmp 26f
25:
26:
	cmp ecx, 2
	jb 27f
	mov eax, DWORD PTR [ebx+16]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [ebx+20]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [ebx+24]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [ebx+28]
	mov DWORD PTR [edi+572], eax
	jmp 28f
27:
28:
	cmp ecx, 3
	jb 29f
	mov eax, DWORD PTR [ebx+32]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [ebx+36]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [ebx+40]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [ebx+44]
	mov DWORD PTR [edi+588], eax
	jmp 210f
29:
210:
	cmp ecx, 4
	jb 211f
	mov eax, DWORD PTR [ebx+48]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [ebx+52]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [ebx+56]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [ebx+60]
	mov DWORD PTR [edi+604], eax
	jmp 212f
211:
212:
	cmp ecx, 5
	jb 213f
	mov eax, DWORD PTR [ebx+64]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [ebx+68]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [ebx+72]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [ebx+76]
	mov DWORD PTR [edi+620], eax
	jmp 214f
213:
214:
	cmp ecx, 6
	jb 215f
	mov eax, DWORD PTR [ebx+80]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [ebx+84]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [ebx+88]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [ebx+92]
	mov DWORD PTR [edi+636], eax
	jmp 216f
215:
216:
	cmp ecx, 7
	jb 217f
	mov eax, DWORD PTR [ebx+96]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [ebx+100]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [ebx+104]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [ebx+108]
	mov DWORD PTR [edi+652], eax
	jmp 218f
217:
218:
	cmp ecx, 8
	jb 219f
	mov eax, DWORD PTR [ebx+112]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [ebx+116]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [ebx+120]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [ebx+124]
	mov DWORD PTR [edi+668], eax
	jmp 220f
219:
220:
	mov DWORD PTR [edi+804], esi
	mov DWORD PTR [edi+812], ebp
	mov DWORD PTR [edi+816], ebx
	mov DWORD PTR [edi+820], edx
	mov eax, DWORD PTR [edi+544]
	bswap eax
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+548]
	bswap eax
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+552]
	bswap eax
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+556]
	bswap eax
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+560]
	bswap eax
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+564]
	bswap eax
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+568]
	bswap eax
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+572]
	bswap eax
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+576]
	bswap eax
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+580]
	bswap eax
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+584]
	bswap eax
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+588]
	bswap eax
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+592]
	bswap eax
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+596]
	bswap eax
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+600]
	bswap eax
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+604]
	bswap eax
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+608]
	bswap eax
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+612]
	bswap eax
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+616]
	bswap eax
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+620]
	bswap eax
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+624]
	bswap eax
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+628]
	bswap eax
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+632]
	bswap eax
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+636]
	bswap eax
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+640]
	bswap eax
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+644]
	bswap eax
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+648]
	bswap eax
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+652]
	bswap eax
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+656]
	bswap eax
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+660]
	bswap eax
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+664]
	bswap eax
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [edi+668]
	bswap eax
	mov DWORD PTR [edi+540], eax
	mov esi, edi
	add esi, 672
221:
	mov ecx, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+480]
	xor eax, ecx
	mov DWORD PTR [edi+320], eax
	xor eax, DWORD PTR [edi+512]
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+484]
	xor eax, ecx
	mov DWORD PTR [edi+324], eax
	xor eax, DWORD PTR [edi+516]
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+488]
	xor eax, ecx
	mov DWORD PTR [edi+328], eax
	xor eax, DWORD PTR [edi+520]
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+492]
	xor eax, ecx
	mov DWORD PTR [edi+332], eax
	xor eax, DWORD PTR [edi+524]
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+496]
	xor eax, ecx
	mov DWORD PTR [edi+336], eax
	xor eax, DWORD PTR [edi+528]
	xor eax, edx
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+500]
	xor eax, ecx
	mov DWORD PTR [edi+340], eax
	xor eax, DWORD PTR [edi+532]
	xor eax, edx
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+504]
	xor eax, ecx
	mov DWORD PTR [edi+344], eax
	xor eax, DWORD PTR [edi+536]
	xor eax, edx
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+508]
	xor eax, ecx
	mov DWORD PTR [edi+348], eax
	xor eax, DWORD PTR [edi+540]
	xor eax, edx
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
	mov DWORD PTR [edi+352], eax
	add eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+356], eax
	add eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+360], eax
	add eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+364], eax
	add eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+368], eax
	add eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+372], eax
	add eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+376], eax
	add eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+380], eax
	add eax, DWORD PTR [edi+348]
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
	mov DWORD PTR [edi+384], eax
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+388], eax
	add eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+392], eax
	add eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+396], eax
	add eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+400], eax
	add eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+404], eax
	add eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+408], eax
	add eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+412], eax
	add eax, DWORD PTR [edi+380]
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
	mov ebx, DWORD PTR [edi+448]
	xor ebx, eax
	mov DWORD PTR [edi+448], ebx
	add eax, DWORD PTR [edi+384]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+452]
	xor ebx, eax
	mov DWORD PTR [edi+452], ebx
	add eax, DWORD PTR [edi+388]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+456]
	xor ebx, eax
	mov DWORD PTR [edi+456], ebx
	add eax, DWORD PTR [edi+392]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+460]
	xor ebx, eax
	mov DWORD PTR [edi+460], ebx
	add eax, DWORD PTR [edi+396]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+464]
	xor ebx, eax
	mov DWORD PTR [edi+464], ebx
	add eax, DWORD PTR [edi+400]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+468]
	xor ebx, eax
	mov DWORD PTR [edi+468], ebx
	add eax, DWORD PTR [edi+404]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+472]
	xor ebx, eax
	mov DWORD PTR [edi+472], ebx
	add eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+476]
	xor ebx, eax
	mov DWORD PTR [edi+476], ebx
	add eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+444], eax
	add esi, 8
	mov ecx, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [edi+416]
	xor eax, ecx
	mov DWORD PTR [edi+320], eax
	xor eax, DWORD PTR [edi+448]
	xor eax, edx
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+420]
	xor eax, ecx
	mov DWORD PTR [edi+324], eax
	xor eax, DWORD PTR [edi+452]
	xor eax, edx
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+424]
	xor eax, ecx
	mov DWORD PTR [edi+328], eax
	xor eax, DWORD PTR [edi+456]
	xor eax, edx
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+428]
	xor eax, ecx
	mov DWORD PTR [edi+332], eax
	xor eax, DWORD PTR [edi+460]
	xor eax, edx
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+432]
	xor eax, ecx
	mov DWORD PTR [edi+336], eax
	xor eax, DWORD PTR [edi+464]
	xor eax, edx
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+436]
	xor eax, ecx
	mov DWORD PTR [edi+340], eax
	xor eax, DWORD PTR [edi+468]
	xor eax, edx
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+440]
	xor eax, ecx
	mov DWORD PTR [edi+344], eax
	xor eax, DWORD PTR [edi+472]
	xor eax, edx
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+444]
	xor eax, ecx
	mov DWORD PTR [edi+348], eax
	xor eax, DWORD PTR [edi+476]
	xor eax, edx
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
	mov DWORD PTR [edi+352], eax
	add eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+356], eax
	add eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+360], eax
	add eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+364], eax
	add eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+368], eax
	add eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+372], eax
	add eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+376], eax
	add eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+380], eax
	add eax, DWORD PTR [edi+348]
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
	mov DWORD PTR [edi+384], eax
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+388], eax
	add eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+392], eax
	add eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+396], eax
	add eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+400], eax
	add eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+404], eax
	add eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+408], eax
	add eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+412], eax
	add eax, DWORD PTR [edi+380]
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
	mov ebx, DWORD PTR [edi+512]
	xor ebx, eax
	mov DWORD PTR [edi+512], ebx
	add eax, DWORD PTR [edi+384]
	xor eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+516]
	xor ebx, eax
	mov DWORD PTR [edi+516], ebx
	add eax, DWORD PTR [edi+388]
	xor eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+520]
	xor ebx, eax
	mov DWORD PTR [edi+520], ebx
	add eax, DWORD PTR [edi+392]
	xor eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+524]
	xor ebx, eax
	mov DWORD PTR [edi+524], ebx
	add eax, DWORD PTR [edi+396]
	xor eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+528]
	xor ebx, eax
	mov DWORD PTR [edi+528], ebx
	add eax, DWORD PTR [edi+400]
	xor eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+532]
	xor ebx, eax
	mov DWORD PTR [edi+532], ebx
	add eax, DWORD PTR [edi+404]
	xor eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+536]
	xor ebx, eax
	mov DWORD PTR [edi+536], ebx
	add eax, DWORD PTR [edi+408]
	xor eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+540]
	xor ebx, eax
	mov DWORD PTR [edi+540], ebx
	add eax, DWORD PTR [edi+412]
	xor eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+508], eax
	add esi, 8
	mov eax, esi
	sub eax, edi
	cmp eax, 800
	jne 221b
	mov eax, DWORD PTR [edi+480]
	bswap eax
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+512]
	bswap eax
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+416]
	bswap eax
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+448]
	bswap eax
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+484]
	bswap eax
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+516]
	bswap eax
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+420]
	bswap eax
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+452]
	bswap eax
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+488]
	bswap eax
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+520]
	bswap eax
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+424]
	bswap eax
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+456]
	bswap eax
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+492]
	bswap eax
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+524]
	bswap eax
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+428]
	bswap eax
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+460]
	bswap eax
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+496]
	bswap eax
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+528]
	bswap eax
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+432]
	bswap eax
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+464]
	bswap eax
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+500]
	bswap eax
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+532]
	bswap eax
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+436]
	bswap eax
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+468]
	bswap eax
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+504]
	bswap eax
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+536]
	bswap eax
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+440]
	bswap eax
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+472]
	bswap eax
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+508]
	bswap eax
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+540]
	bswap eax
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+444]
	bswap eax
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+476]
	bswap eax
	mov DWORD PTR [edi+668], eax
	mov esi, DWORD PTR [edi+804]
	mov ebp, DWORD PTR [edi+812]
	mov ebx, DWORD PTR [edi+816]
	mov edx, DWORD PTR [edi+820]
	mov ecx, edx
	cmp edx, 8
	jb 222f
	mov ecx, 8
	jmp 223f
222:
223:
	cmp ecx, 1
	jb 224f
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [ebx+12], eax
	jmp 225f
224:
225:
	cmp ecx, 2
	jb 226f
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [ebx+24], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [ebx+28], eax
	jmp 227f
226:
227:
	cmp ecx, 3
	jb 228f
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [ebx+32], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [ebx+40], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [ebx+44], eax
	jmp 229f
228:
229:
	cmp ecx, 4
	jb 230f
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [ebx+48], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [ebx+52], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [ebx+56], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [ebx+60], eax
	jmp 231f
230:
231:
	cmp ecx, 5
	jb 232f
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [ebx+64], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [ebx+68], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [ebx+72], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [ebx+76], eax
	jmp 233f
232:
233:
	cmp ecx, 6
	jb 234f
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [ebx+80], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [ebx+84], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [ebx+88], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [ebx+92], eax
	jmp 235f
234:
235:
	cmp ecx, 7
	jb 236f
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [ebx+96], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [ebx+100], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [ebx+104], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [ebx+108], eax
	jmp 237f
236:
237:
	cmp ecx, 8
	jb 238f
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [ebx+112], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [ebx+116], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [ebx+120], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [ebx+124], eax
	jmp 239f
238:
239:
	add ebx, 128
	sub edx, ecx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [edi+800]
	mov edi, DWORD PTR [edi+808]
	ret
	.p2align 6
