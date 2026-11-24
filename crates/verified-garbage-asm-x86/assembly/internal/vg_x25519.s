// The functions of `src/internal/vg_x25519.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
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
	and eax, 2147483647
	mov DWORD PTR [edi+316], eax
	mov esi, DWORD PTR [esp+8]
	mov ebx, edi
	add ebx, 32
	mov ecx, 32
20:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+1], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+2], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+3], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+5], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+6], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+7], dl
	add esi, 1
	add ebx, 8
	sub ecx, 1
	jne 20b
	mov edx, 0
	mov BYTE PTR [edi+32], dl
	mov BYTE PTR [edi+33], dl
	mov BYTE PTR [edi+34], dl
	mov edx, 1
	mov BYTE PTR [edi+286], dl
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+412], eax
	mov eax, 1
	mov DWORD PTR [edi+320], eax
	mov eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, 0
	mov DWORD PTR [edi+352], eax
	mov eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, 1
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+16], eax
	mov esi, 255
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+32]
	mov edx, DWORD PTR [edi+16]
	xor edx, eax
	mov DWORD PTR [edi+16], eax
	mov ecx, 0
	sub ecx, edx
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+384]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+384], edx
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+388]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+388], edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+392]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+392], edx
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+396]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+396], edx
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+400]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+400], edx
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+404]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+404], edx
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+408]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+408], edx
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+412]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+416]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+416], edx
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+420]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+424]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+424], edx
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+428]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+432]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+432], edx
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+436]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+440]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+440], edx
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+444]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+444], edx
	xor ecx, ecx
	mov eax, DWORD PTR [edi+320]
	adc eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+324]
	adc eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+328]
	adc eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+332]
	adc eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+336]
	adc eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+340]
	adc eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+344]
	adc eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+348]
	adc eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+476], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+448]
	adc eax, ecx
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+452]
	adc eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+456]
	adc eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+460]
	adc eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+464]
	adc eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+468]
	adc eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+472]
	adc eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+476]
	adc eax, 0
	mov DWORD PTR [edi+476], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+448]
	adc eax, ecx
	mov DWORD PTR [edi+448], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+452]
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
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+456]
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
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+460]
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
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+464]
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
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+468]
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
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+472]
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
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+476]
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
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+476]
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
	mov DWORD PTR [edi+576], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+580], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+584], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+588], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+592], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+596], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+600], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+604], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+576]
	adc eax, ecx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+580]
	adc eax, 0
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+584]
	adc eax, 0
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+588]
	adc eax, 0
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+592]
	adc eax, 0
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+596]
	adc eax, 0
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+600]
	adc eax, 0
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+604]
	adc eax, 0
	mov DWORD PTR [edi+604], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+576]
	adc eax, ecx
	mov DWORD PTR [edi+576], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+320]
	sbb eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+324]
	sbb eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+328]
	sbb eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+332]
	sbb eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+336]
	sbb eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+340]
	sbb eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+344]
	sbb eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+348]
	sbb eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+508], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+480]
	sbb eax, ecx
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+484]
	sbb eax, 0
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+488]
	sbb eax, 0
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+492]
	sbb eax, 0
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+496]
	sbb eax, 0
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+500]
	sbb eax, 0
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+504]
	sbb eax, 0
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+508]
	sbb eax, 0
	mov DWORD PTR [edi+508], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+480]
	sbb eax, ecx
	mov DWORD PTR [edi+480], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+484]
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
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+488]
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
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+492]
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
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+496]
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
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+500]
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
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+504]
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
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+508]
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
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+508]
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
	mov DWORD PTR [edi+608], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+612], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+616], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+620], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+624], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+628], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+632], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+636], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+608]
	adc eax, ecx
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+612]
	adc eax, 0
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+616]
	adc eax, 0
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+620]
	adc eax, 0
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+624]
	adc eax, 0
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+628]
	adc eax, 0
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+632]
	adc eax, 0
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+636]
	adc eax, 0
	mov DWORD PTR [edi+636], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+608]
	adc eax, ecx
	mov DWORD PTR [edi+608], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+576]
	sbb eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+580]
	sbb eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+584]
	sbb eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+588]
	sbb eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+592]
	sbb eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+596]
	sbb eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+600]
	sbb eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+604]
	sbb eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+668], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+640]
	sbb eax, ecx
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+644]
	sbb eax, 0
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+648]
	sbb eax, 0
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+652]
	sbb eax, 0
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+656]
	sbb eax, 0
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+660]
	sbb eax, 0
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+664]
	sbb eax, 0
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+668]
	sbb eax, 0
	mov DWORD PTR [edi+668], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+640]
	sbb eax, ecx
	mov DWORD PTR [edi+640], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+384]
	adc eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+540], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+512]
	adc eax, ecx
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+516]
	adc eax, 0
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+520]
	adc eax, 0
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+524]
	adc eax, 0
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+528]
	adc eax, 0
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+532]
	adc eax, 0
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+536]
	adc eax, 0
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+540]
	adc eax, 0
	mov DWORD PTR [edi+540], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+512]
	adc eax, ecx
	mov DWORD PTR [edi+512], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+384]
	sbb eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+388]
	sbb eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+392]
	sbb eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+396]
	sbb eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+400]
	sbb eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+404]
	sbb eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+408]
	sbb eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+412]
	sbb eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	sbb eax, ecx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+548]
	sbb eax, 0
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+552]
	sbb eax, 0
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+556]
	sbb eax, 0
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+560]
	sbb eax, 0
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+564]
	sbb eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+568]
	sbb eax, 0
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	sbb eax, 0
	mov DWORD PTR [edi+572], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+544]
	sbb eax, ecx
	mov DWORD PTR [edi+544], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+476]
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
	mov DWORD PTR [edi+672], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+676], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+680], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+684], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+688], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+692], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+696], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+700], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+672]
	adc eax, ecx
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+676]
	adc eax, 0
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+680]
	adc eax, 0
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+684]
	adc eax, 0
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+688]
	adc eax, 0
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+692]
	adc eax, 0
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+696]
	adc eax, 0
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+700]
	adc eax, 0
	mov DWORD PTR [edi+700], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+672]
	adc eax, ecx
	mov DWORD PTR [edi+672], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+508]
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
	mov DWORD PTR [edi+704], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+708], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+712], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+716], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+720], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+724], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+728], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+732], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+704]
	adc eax, ecx
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+708]
	adc eax, 0
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+712]
	adc eax, 0
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+716]
	adc eax, 0
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+720]
	adc eax, 0
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+724]
	adc eax, 0
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+728]
	adc eax, 0
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+732]
	adc eax, 0
	mov DWORD PTR [edi+732], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+704]
	adc eax, ecx
	mov DWORD PTR [edi+704], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+672]
	adc eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+676]
	adc eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+680]
	adc eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+684]
	adc eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+688]
	adc eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+692]
	adc eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+696]
	adc eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+700]
	adc eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+388]
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
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+392]
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
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+396]
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
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+400]
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
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+404]
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
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+408]
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
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+412]
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
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+412]
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
	mov DWORD PTR [edi+384], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+388], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+392], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+396], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+400], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+404], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+408], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+412], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+388]
	adc eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+392]
	adc eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+396]
	adc eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+400]
	adc eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+404]
	adc eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+408]
	adc eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+412]
	adc eax, 0
	mov DWORD PTR [edi+412], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+384]
	adc eax, ecx
	mov DWORD PTR [edi+384], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+672]
	sbb eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+676]
	sbb eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+680]
	sbb eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+684]
	sbb eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+688]
	sbb eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+692]
	sbb eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+696]
	sbb eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+700]
	sbb eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	sbb eax, ecx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+420]
	sbb eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+424]
	sbb eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+428]
	sbb eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+432]
	sbb eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+436]
	sbb eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+440]
	sbb eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+444]
	sbb eax, 0
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	sbb eax, ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+420]
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
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+424]
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
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+428]
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
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+432]
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
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+436]
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
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+440]
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
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+444]
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
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+444]
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
	mov DWORD PTR [edi+416], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+420], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+424], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+428], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+432], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+436], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+440], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+444], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+420]
	adc eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+424]
	adc eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+428]
	adc eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+432]
	adc eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+436]
	adc eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+440]
	adc eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+444]
	adc eax, 0
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+416]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+420]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+424]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+428]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+432]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+436]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+444]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+440]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+444]
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
	mov DWORD PTR [edi+416], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+420], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+424], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+428], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+432], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+436], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+440], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+444], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+420]
	adc eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+424]
	adc eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+428]
	adc eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+432]
	adc eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+436]
	adc eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+440]
	adc eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+444]
	adc eax, 0
	mov DWORD PTR [edi+444], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+416]
	adc eax, ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+636]
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
	mov DWORD PTR [edi+320], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+324], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+328], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+332], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+336], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+340], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+344], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+348], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+324]
	adc eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+328]
	adc eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+332]
	adc eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+336]
	adc eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	adc eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	adc eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	adc eax, 0
	mov DWORD PTR [edi+348], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, 121665
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+380], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+380], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+352], eax
	xor ecx, ecx
	mov eax, DWORD PTR [edi+576]
	adc eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+580]
	adc eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+584]
	adc eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+588]
	adc eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+592]
	adc eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+596]
	adc eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+600]
	adc eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+604]
	adc eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	adc eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	adc eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	adc eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+368]
	adc eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+372]
	adc eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+376]
	adc eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+380]
	adc eax, 0
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+380]
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
	mov DWORD PTR [edi+352], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+356], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+360], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+364], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+368], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+372], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+376], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+380], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	adc eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	adc eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	adc eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+368]
	adc eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+372]
	adc eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+376]
	adc eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+380]
	adc eax, 0
	mov DWORD PTR [edi+380], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+352]
	adc eax, ecx
	mov DWORD PTR [edi+352], eax
	test esi, esi
	jne 21b
	mov edx, DWORD PTR [edi+16]
	mov ecx, 0
	sub ecx, edx
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+384]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+320], eax
	mov DWORD PTR [edi+384], edx
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+388]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+324], eax
	mov DWORD PTR [edi+388], edx
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+392]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+328], eax
	mov DWORD PTR [edi+392], edx
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+396]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+332], eax
	mov DWORD PTR [edi+396], edx
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+400]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+336], eax
	mov DWORD PTR [edi+400], edx
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+404]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+340], eax
	mov DWORD PTR [edi+404], edx
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+408]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+344], eax
	mov DWORD PTR [edi+408], edx
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+412]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+348], eax
	mov DWORD PTR [edi+412], edx
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+416]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+352], eax
	mov DWORD PTR [edi+416], edx
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+420]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+356], eax
	mov DWORD PTR [edi+420], edx
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+424]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+360], eax
	mov DWORD PTR [edi+424], edx
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+428]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+364], eax
	mov DWORD PTR [edi+428], edx
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+432]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+368], eax
	mov DWORD PTR [edi+432], edx
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+436]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+372], eax
	mov DWORD PTR [edi+436], edx
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+440]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+376], eax
	mov DWORD PTR [edi+440], edx
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+444]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+380], eax
	mov DWORD PTR [edi+444], edx
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+156], eax
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
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
	mov DWORD PTR [edi+320], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+900]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+868]
	adc edx, 0
	mov DWORD PTR [edi+324], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+904]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+872]
	adc edx, 0
	mov DWORD PTR [edi+328], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+908]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+876]
	adc edx, 0
	mov DWORD PTR [edi+332], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+912]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+880]
	adc edx, 0
	mov DWORD PTR [edi+336], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+916]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+884]
	adc edx, 0
	mov DWORD PTR [edi+340], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+920]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+888]
	adc edx, 0
	mov DWORD PTR [edi+344], eax
	mov ebx, edx
	mov eax, DWORD PTR [edi+924]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [edi+892]
	adc edx, 0
	mov DWORD PTR [edi+348], eax
	mov ebx, edx
	mov eax, 38
	mul ebx
	mov ecx, eax
	test ecx, ecx
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+324]
	adc eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+328]
	adc eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+332]
	adc eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+336]
	adc eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	adc eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	adc eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	adc eax, 0
	mov DWORD PTR [edi+348], eax
	sbb ecx, ecx
	and ecx, 38
	mov eax, DWORD PTR [edi+320]
	adc eax, ecx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+348]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
	and eax, 2147483647
	mov DWORD PTR [edi+348], eax
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+348], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+348], eax
	mov esi, DWORD PTR [esp+4]
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
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6
