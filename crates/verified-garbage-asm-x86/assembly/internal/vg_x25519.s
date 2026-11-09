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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+476], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+448]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+452]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+456]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+460]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+464]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+468]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+472]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+476]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+476], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+448]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+576], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+580], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+584], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+588], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+592], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+596], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+600], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+604], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+576]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+576], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+580]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+580], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+584]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+584], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+588]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+588], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+592]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+592], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+596]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+596], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+600]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+600], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+604]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+604], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+576], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+352]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+480], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+484], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+488], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+492], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+496], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+500], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+504], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+508], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+480]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+480], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+484]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+484], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+488]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+488], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+492]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+492], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+496]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+496], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+500]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+500], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+504]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+504], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+508]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+508], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+480]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+608], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+612], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+616], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+620], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+624], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+628], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+632], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+636], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+608]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+608], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+612]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+612], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+616]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+616], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+620]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+620], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+624]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+624], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+628]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+628], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+632]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+632], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+636]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+636], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+608], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+576]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+608]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+640], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+580]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+612]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+644], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+584]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+616]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+588]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+620]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+592]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+624]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+596]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+628]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+600]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+632]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+664], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+604]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+636]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+668], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+640]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+640], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+644]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+644], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+648]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+652]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+656]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+660]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+664]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+664], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+668]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+668], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+640], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+512]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+516]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+520]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+524]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+528]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+532]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+536]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+540]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+540], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+512], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+416]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+544]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+548]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+552]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+556]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+560]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+564]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+568]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+572]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+544]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+672], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+676], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+680], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+684], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+688], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+692], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+672]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+672], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+676]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+676], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+680]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+680], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+684]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+684], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+688]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+688], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+692]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+692], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+696]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+700]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+672]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+712], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+716], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+720], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+724], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+728], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+732], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+704]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+708]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+712]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+712], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+716]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+716], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+720]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+720], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+724]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+724], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+728]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+728], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+732]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+732], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+704], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+672]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+704]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+676]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+708]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+680]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+712]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+684]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+716]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+688]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+720]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+692]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+724]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+696]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+728]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+700]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+732]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+384]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+412], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+384], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+672]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+704]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+676]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+680]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+684]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+688]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+692]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+696]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+700]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+416]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+416]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+444], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+416]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+348], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+320]
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+576]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+580]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+584]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+588]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+592]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+596]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+600]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+604]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
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
	push edi
	call {vg_gf25519_r32_pow250}
	pop eax
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+544]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+548]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+552]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+556]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+560]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+564]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+568]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+572]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+544]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+544]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+544], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+548]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+548], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+552]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+552], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+556]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+556], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+560]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+560], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+564]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+564], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+568]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+568], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+572]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+572], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+544]
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
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+896]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+900]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+868]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+904]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+908]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+912]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+916]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+920]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+924]
	mov edx, 38
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+348], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+320]
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
