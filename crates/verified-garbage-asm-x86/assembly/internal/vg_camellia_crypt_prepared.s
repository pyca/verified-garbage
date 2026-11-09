// The functions of `src/internal/vg_camellia_crypt_prepared.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_crypt_prepared:
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [eax+2620], ebx
	mov DWORD PTR [eax+2624], esi
	mov DWORD PTR [eax+2628], edi
	mov DWORD PTR [eax+2632], ebp
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	cmp eax, 18
	je 20f
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+400]
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
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+404]
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
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+408]
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
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+412]
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
	mov esi, edi
	add esi, 416
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+284], eax
	add esi, 128
22:
	mov eax, esi
	add eax, 384
	mov DWORD PTR [edi+2616], eax
23:
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	xor ebx, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	xor ebx, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	xor ebx, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	xor ebx, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	xor ebx, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	xor ebx, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	xor ebx, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	xor ebx, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	add esi, 128
	mov eax, DWORD PTR [edi+2616]
	cmp eax, esi
	jne 23b
	mov eax, esi
	sub eax, edi
	cmp eax, 2464
	jne 24f
	jmp 25f
24:
	mov eax, DWORD PTR [esi+96]
	or eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [esi+100]
	or eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [esi+104]
	or eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [esi+108]
	or eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [esi+112]
	or eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [esi+116]
	or eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [esi+120]
	or eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [esi+124]
	or eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [edi+252]
	ror eax, 8
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+188]
	ror eax, 8
	xor eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [esi+32]
	or eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	or eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	or eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	or eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	or eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	or eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	or eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	or eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	add esi, 128
25:
	mov eax, esi
	sub eax, edi
	cmp eax, 2464
	jne 22b
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
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
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
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
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
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
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
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
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+412], eax
	jmp 21f
20:
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+400]
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
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+404]
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
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+408]
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
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+412]
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
	mov esi, edi
	add esi, 416
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+284], eax
	add esi, 128
26:
	mov eax, esi
	add eax, 384
	mov DWORD PTR [edi+2616], eax
27:
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	xor ebx, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	xor ebx, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	xor ebx, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	xor ebx, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	xor ebx, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	xor ebx, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	xor ebx, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	xor ebx, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, -16777216
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 16711680
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+8]
	xor ecx, eax
	mov edx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi]
	xor ebp, ebx
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ecx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, ebx
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+8]
	xor ebx, edx
	mov DWORD PTR [edi+48], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [edi+52], ebx
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, edx
	xor eax, -1
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, ecx
	xor edx, DWORD PTR [edi+16]
	xor ebx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, DWORD PTR [edi]
	xor edx, -1
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+8]
	xor edx, ebp
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+36]
	xor eax, -1
	mov DWORD PTR [edi+88], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov DWORD PTR [edi+92], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, ebp
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+44]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, ebp
	xor eax, -1
	xor ecx, DWORD PTR [edi+64]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+36]
	xor ebp, -1
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+72]
	xor ecx, -1
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	xor ebp, -1
	xor edx, DWORD PTR [edi+48]
	xor edx, -1
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+24]
	xor edx, -1
	xor edx, DWORD PTR [edi+24]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+4]
	xor eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+32]
	and eax, ebx
	mov DWORD PTR [edi+104], ebx
	mov ebx, edx
	and ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+108], edx
	mov edx, DWORD PTR [edi+40]
	and edx, ecx
	xor edx, eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+84]
	xor ecx, eax
	mov DWORD PTR [edi+116], ebp
	mov ebp, DWORD PTR [edi+52]
	and ebp, DWORD PTR [edi+80]
	xor ebp, eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+120], ebp
	mov ebp, DWORD PTR [edi+72]
	and ebp, DWORD PTR [edi+48]
	xor ebp, eax
	mov DWORD PTR [edi+124], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+60]
	xor ecx, eax
	xor ebx, ebp
	xor edx, ecx
	xor ebp, DWORD PTR [edi+124]
	xor ecx, DWORD PTR [edi+120]
	xor ebx, DWORD PTR [edi+44]
	xor edx, DWORD PTR [edi+96]
	xor ebp, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+36]
	mov eax, ebx
	xor eax, edx
	and ebx, ebp
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, eax
	and ebx, ebp
	xor ebx, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	xor edx, DWORD PTR [edi+64]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+36]
	xor eax, edx
	mov DWORD PTR [edi+36], ebx
	mov ebx, ebp
	xor ebx, edx
	and ecx, ebx
	xor eax, ecx
	xor ebp, ecx
	and ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, eax
	mov ebx, DWORD PTR [edi+36]
	xor ebx, edx
	mov DWORD PTR [edi+96], ebx
	mov ebx, DWORD PTR [edi+36]
	xor ebx, ebp
	mov DWORD PTR [edi+64], ebp
	mov ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+96]
	xor ebx, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+96]
	and ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ecx
	mov ecx, DWORD PTR [edi+120]
	and ecx, DWORD PTR [edi+60]
	and ebp, DWORD PTR [edi+32]
	and eax, DWORD PTR [edi+108]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+44]
	and eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, DWORD PTR [edi+36]
	and ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+96]
	and ebp, DWORD PTR [edi+76]
	and ebx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+120]
	and ebp, DWORD PTR [edi+92]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+68]
	xor eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, ecx
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, ebx
	xor edx, ebp
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+48]
	xor ebp, DWORD PTR [edi+68]
	mov DWORD PTR [edi+96], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, eax
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+100]
	xor eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+88]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+56]
	xor eax, ebp
	xor ebx, edx
	mov DWORD PTR [edi+56], ebx
	mov ebx, ecx
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	xor eax, DWORD PTR [edi+84]
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+100]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+72]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+92]
	xor ecx, DWORD PTR [edi+120]
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+88]
	mov DWORD PTR [edi+88], ebx
	mov ebx, DWORD PTR [edi+52]
	xor ebx, DWORD PTR [edi+120]
	xor eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+120], edx
	mov edx, DWORD PTR [edi+112]
	xor edx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+64]
	xor ecx, DWORD PTR [edi+76]
	xor ecx, -1
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+40]
	xor ecx, DWORD PTR [edi+80]
	xor ebx, DWORD PTR [edi+96]
	xor ebx, -1
	xor edx, DWORD PTR [edi+92]
	xor edx, -1
	xor ebp, eax
	xor ecx, DWORD PTR [edi+100]
	xor ecx, -1
	mov DWORD PTR [edi+28], ebp
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+12], ebx
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi]
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 255
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+4]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+8]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+12]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+16]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+20]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+24]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov ebx, eax
	xor ebx, DWORD PTR [edi+28]
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov ebx, eax
	xor ebx, ecx
	and ebx, 65280
	xor eax, ebx
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+128]
	mov ebx, DWORD PTR [edi]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+132]
	mov ebx, DWORD PTR [edi+4]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi+136]
	mov ebx, DWORD PTR [edi+8]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+140]
	mov ebx, DWORD PTR [edi+12]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+144]
	mov ebx, DWORD PTR [edi+16]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+148]
	mov ebx, DWORD PTR [edi+20]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+152]
	mov ebx, DWORD PTR [edi+24]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+156]
	mov ebx, DWORD PTR [edi+28]
	xor eax, ebx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor ebx, eax
	mov ecx, eax
	ror ecx, 8
	xor ebx, ecx
	mov ecx, ebx
	ror ecx, 16
	xor eax, ecx
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	add esi, 128
	mov eax, DWORD PTR [edi+2616]
	cmp eax, esi
	jne 27b
	mov eax, esi
	sub eax, edi
	cmp eax, 1952
	jne 28f
	jmp 29f
28:
	mov eax, DWORD PTR [esi+96]
	or eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [esi+100]
	or eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [esi+104]
	or eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [esi+108]
	or eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [esi+112]
	or eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [esi+116]
	or eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [esi+120]
	or eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [esi+124]
	or eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [edi+252]
	ror eax, 8
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [esi+28]
	and eax, DWORD PTR [edi+188]
	ror eax, 8
	xor eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [esi]
	and eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [esi+4]
	and eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [esi+8]
	and eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [esi+12]
	and eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [esi+16]
	and eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [esi+20]
	and eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [esi+24]
	and eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [esi+32]
	or eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	or eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	or eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	or eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	or eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	or eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	or eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	or eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], eax
	add esi, 128
29:
	mov eax, esi
	sub eax, edi
	cmp eax, 1952
	jne 26b
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+256]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+260]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+264]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+268]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+272]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+276]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+280]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+284]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
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
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+284]
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
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
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
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
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
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+412], eax
21:
	mov ebx, DWORD PTR [edi+2620]
	mov esi, DWORD PTR [edi+2624]
	mov ebp, DWORD PTR [edi+2632]
	mov edi, DWORD PTR [edi+2628]
	ret
	.p2align 6
