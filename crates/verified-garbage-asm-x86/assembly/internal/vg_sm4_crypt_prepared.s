// The functions of `src/internal/vg_sm4_crypt_prepared.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_crypt_prepared:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+1408], ebx
	mov DWORD PTR [eax+1412], esi
	mov DWORD PTR [eax+1416], edi
	mov DWORD PTR [eax+1420], ebp
	mov edi, eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+368]
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
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+372]
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
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+376]
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
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+380]
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
	mov esi, edi
	add esi, 384
20:
	mov eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	xor ecx, ebx
	mov edx, DWORD PTR [edi+28]
	xor edx, eax
	mov ebp, DWORD PTR [edi+20]
	xor ebp, ecx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ebp
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ecx
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	xor ebp, DWORD PTR [edi+4]
	xor ebp, -1
	mov DWORD PTR [edi+60], ebp
	mov ebp, ebx
	xor ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi]
	xor ebx, edx
	xor edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+68], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+24]
	mov DWORD PTR [edi+72], edx
	mov edx, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+44]
	xor edx, -1
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, ecx
	xor edx, -1
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+32]
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+40]
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+8]
	xor ebp, -1
	xor ebx, DWORD PTR [edi+4]
	xor ebx, -1
	xor ecx, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+52]
	xor ebx, -1
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+4]
	xor ebp, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+32], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+100], ebp
	mov ebp, DWORD PTR [edi+40]
	and ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+84]
	and edx, DWORD PTR [edi+80]
	xor edx, eax
	mov eax, DWORD PTR [edi+4]
	and eax, ecx
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, ebx
	xor ecx, eax
	mov DWORD PTR [edi+112], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+76]
	xor ebx, eax
	mov eax, DWORD PTR [edi+56]
	and eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+116], ebx
	mov ebx, DWORD PTR [edi+48]
	and ebx, DWORD PTR [edi+32]
	xor ebx, eax
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+44]
	xor ecx, eax
	xor ebp, ebx
	xor edx, ecx
	xor ebx, DWORD PTR [edi+120]
	xor ecx, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+68]
	xor ebx, DWORD PTR [edi+88]
	xor ecx, DWORD PTR [edi+64]
	mov eax, ebp
	xor eax, edx
	and ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	xor ebx, ebp
	mov DWORD PTR [edi+88], ebp
	mov ebp, eax
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+64]
	xor eax, ecx
	xor edx, DWORD PTR [edi+88]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+64]
	xor eax, edx
	mov DWORD PTR [edi+64], ebp
	mov ebp, ebx
	xor ebp, edx
	and ecx, ebp
	xor eax, ecx
	xor ebx, ecx
	and ebx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+68]
	mov ecx, ebx
	xor ecx, eax
	mov ebp, DWORD PTR [edi+64]
	xor ebp, edx
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+64]
	xor ebp, ebx
	mov DWORD PTR [edi+88], ebx
	mov ebx, edx
	xor ebx, eax
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+68]
	xor ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+60]
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+88]
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+116]
	and ecx, DWORD PTR [edi+44]
	and ebx, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], edx
	mov edx, DWORD PTR [edi+52]
	and edx, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+56]
	and ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+116]
	and ebp, DWORD PTR [edi+92]
	xor ebx, ecx
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+60]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], eax
	mov eax, edx
	xor eax, ecx
	xor eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, eax
	xor ebp, ebx
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+56], ebx
	mov ebx, edx
	xor ebx, ebp
	mov DWORD PTR [edi+68], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, eax
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+48]
	xor edx, ecx
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+108]
	xor ebx, DWORD PTR [edi+76]
	xor ebx, edx
	xor ebp, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+72]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, DWORD PTR [edi+116]
	xor ecx, -1
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, DWORD PTR [edi+80]
	xor ecx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+32]
	xor ebx, -1
	xor ebp, edx
	xor ebp, -1
	mov edx, DWORD PTR [edi+60]
	xor edx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ebp
	mov ebp, DWORD PTR [edi+108]
	xor ebp, DWORD PTR [edi+68]
	xor edx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+48]
	xor eax, -1
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+20], edx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+8], ebp
	mov DWORD PTR [edi], ebx
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+24]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+128]
	mov DWORD PTR [edi+128], ebx
	mov eax, DWORD PTR [edi+28]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+4]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+132]
	mov DWORD PTR [edi+132], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+8]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+136]
	mov DWORD PTR [edi+136], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+12]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+140]
	mov DWORD PTR [edi+140], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+16]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+144]
	mov DWORD PTR [edi+144], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+20]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+148]
	mov DWORD PTR [edi+148], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+24]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+152]
	mov DWORD PTR [edi+152], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+28]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+156]
	mov DWORD PTR [edi+156], ebx
	mov eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+128]
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+132]
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+136]
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+140]
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+144]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+148]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+152]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [edi+156]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	xor ecx, ebx
	mov edx, DWORD PTR [edi+28]
	xor edx, eax
	mov ebp, DWORD PTR [edi+20]
	xor ebp, ecx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ebp
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ecx
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	xor ebp, DWORD PTR [edi+4]
	xor ebp, -1
	mov DWORD PTR [edi+60], ebp
	mov ebp, ebx
	xor ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi]
	xor ebx, edx
	xor edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+68], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+24]
	mov DWORD PTR [edi+72], edx
	mov edx, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+44]
	xor edx, -1
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, ecx
	xor edx, -1
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+32]
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+40]
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+8]
	xor ebp, -1
	xor ebx, DWORD PTR [edi+4]
	xor ebx, -1
	xor ecx, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+52]
	xor ebx, -1
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+4]
	xor ebp, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+32], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+100], ebp
	mov ebp, DWORD PTR [edi+40]
	and ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+84]
	and edx, DWORD PTR [edi+80]
	xor edx, eax
	mov eax, DWORD PTR [edi+4]
	and eax, ecx
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, ebx
	xor ecx, eax
	mov DWORD PTR [edi+112], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+76]
	xor ebx, eax
	mov eax, DWORD PTR [edi+56]
	and eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+116], ebx
	mov ebx, DWORD PTR [edi+48]
	and ebx, DWORD PTR [edi+32]
	xor ebx, eax
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+44]
	xor ecx, eax
	xor ebp, ebx
	xor edx, ecx
	xor ebx, DWORD PTR [edi+120]
	xor ecx, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+68]
	xor ebx, DWORD PTR [edi+88]
	xor ecx, DWORD PTR [edi+64]
	mov eax, ebp
	xor eax, edx
	and ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	xor ebx, ebp
	mov DWORD PTR [edi+88], ebp
	mov ebp, eax
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+64]
	xor eax, ecx
	xor edx, DWORD PTR [edi+88]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+64]
	xor eax, edx
	mov DWORD PTR [edi+64], ebp
	mov ebp, ebx
	xor ebp, edx
	and ecx, ebp
	xor eax, ecx
	xor ebx, ecx
	and ebx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+68]
	mov ecx, ebx
	xor ecx, eax
	mov ebp, DWORD PTR [edi+64]
	xor ebp, edx
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+64]
	xor ebp, ebx
	mov DWORD PTR [edi+88], ebx
	mov ebx, edx
	xor ebx, eax
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+68]
	xor ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+60]
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+88]
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+116]
	and ecx, DWORD PTR [edi+44]
	and ebx, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], edx
	mov edx, DWORD PTR [edi+52]
	and edx, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+56]
	and ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+116]
	and ebp, DWORD PTR [edi+92]
	xor ebx, ecx
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+60]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], eax
	mov eax, edx
	xor eax, ecx
	xor eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, eax
	xor ebp, ebx
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+56], ebx
	mov ebx, edx
	xor ebx, ebp
	mov DWORD PTR [edi+68], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, eax
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+48]
	xor edx, ecx
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+108]
	xor ebx, DWORD PTR [edi+76]
	xor ebx, edx
	xor ebp, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+72]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, DWORD PTR [edi+116]
	xor ecx, -1
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, DWORD PTR [edi+80]
	xor ecx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+32]
	xor ebx, -1
	xor ebp, edx
	xor ebp, -1
	mov edx, DWORD PTR [edi+60]
	xor edx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ebp
	mov ebp, DWORD PTR [edi+108]
	xor ebp, DWORD PTR [edi+68]
	xor edx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+48]
	xor eax, -1
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+20], edx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+8], ebp
	mov DWORD PTR [edi], ebx
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+24]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], ebx
	mov eax, DWORD PTR [edi+28]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+4]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+164]
	mov DWORD PTR [edi+164], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+8]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+168]
	mov DWORD PTR [edi+168], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+12]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+172]
	mov DWORD PTR [edi+172], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+16]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+176]
	mov DWORD PTR [edi+176], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+20]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+180]
	mov DWORD PTR [edi+180], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+24]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+184]
	mov DWORD PTR [edi+184], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+28]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+188]
	mov DWORD PTR [edi+188], ebx
	mov eax, DWORD PTR [edi+224]
	xor eax, DWORD PTR [edi+128]
	xor eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+228]
	xor eax, DWORD PTR [edi+132]
	xor eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+232]
	xor eax, DWORD PTR [edi+136]
	xor eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+236]
	xor eax, DWORD PTR [edi+140]
	xor eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+240]
	xor eax, DWORD PTR [edi+144]
	xor eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+244]
	xor eax, DWORD PTR [edi+148]
	xor eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+248]
	xor eax, DWORD PTR [edi+152]
	xor eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+252]
	xor eax, DWORD PTR [edi+156]
	xor eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	xor ecx, ebx
	mov edx, DWORD PTR [edi+28]
	xor edx, eax
	mov ebp, DWORD PTR [edi+20]
	xor ebp, ecx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ebp
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ecx
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	xor ebp, DWORD PTR [edi+4]
	xor ebp, -1
	mov DWORD PTR [edi+60], ebp
	mov ebp, ebx
	xor ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi]
	xor ebx, edx
	xor edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+68], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+24]
	mov DWORD PTR [edi+72], edx
	mov edx, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+44]
	xor edx, -1
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, ecx
	xor edx, -1
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+32]
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+40]
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+8]
	xor ebp, -1
	xor ebx, DWORD PTR [edi+4]
	xor ebx, -1
	xor ecx, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+52]
	xor ebx, -1
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+4]
	xor ebp, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+32], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+100], ebp
	mov ebp, DWORD PTR [edi+40]
	and ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+84]
	and edx, DWORD PTR [edi+80]
	xor edx, eax
	mov eax, DWORD PTR [edi+4]
	and eax, ecx
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, ebx
	xor ecx, eax
	mov DWORD PTR [edi+112], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+76]
	xor ebx, eax
	mov eax, DWORD PTR [edi+56]
	and eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+116], ebx
	mov ebx, DWORD PTR [edi+48]
	and ebx, DWORD PTR [edi+32]
	xor ebx, eax
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+44]
	xor ecx, eax
	xor ebp, ebx
	xor edx, ecx
	xor ebx, DWORD PTR [edi+120]
	xor ecx, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+68]
	xor ebx, DWORD PTR [edi+88]
	xor ecx, DWORD PTR [edi+64]
	mov eax, ebp
	xor eax, edx
	and ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	xor ebx, ebp
	mov DWORD PTR [edi+88], ebp
	mov ebp, eax
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+64]
	xor eax, ecx
	xor edx, DWORD PTR [edi+88]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+64]
	xor eax, edx
	mov DWORD PTR [edi+64], ebp
	mov ebp, ebx
	xor ebp, edx
	and ecx, ebp
	xor eax, ecx
	xor ebx, ecx
	and ebx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+68]
	mov ecx, ebx
	xor ecx, eax
	mov ebp, DWORD PTR [edi+64]
	xor ebp, edx
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+64]
	xor ebp, ebx
	mov DWORD PTR [edi+88], ebx
	mov ebx, edx
	xor ebx, eax
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+68]
	xor ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+60]
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+88]
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+116]
	and ecx, DWORD PTR [edi+44]
	and ebx, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], edx
	mov edx, DWORD PTR [edi+52]
	and edx, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+56]
	and ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+116]
	and ebp, DWORD PTR [edi+92]
	xor ebx, ecx
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+60]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], eax
	mov eax, edx
	xor eax, ecx
	xor eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, eax
	xor ebp, ebx
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+56], ebx
	mov ebx, edx
	xor ebx, ebp
	mov DWORD PTR [edi+68], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, eax
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+48]
	xor edx, ecx
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+108]
	xor ebx, DWORD PTR [edi+76]
	xor ebx, edx
	xor ebp, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+72]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, DWORD PTR [edi+116]
	xor ecx, -1
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, DWORD PTR [edi+80]
	xor ecx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+32]
	xor ebx, -1
	xor ebp, edx
	xor ebp, -1
	mov edx, DWORD PTR [edi+60]
	xor edx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ebp
	mov ebp, DWORD PTR [edi+108]
	xor ebp, DWORD PTR [edi+68]
	xor edx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+48]
	xor eax, -1
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+20], edx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+8], ebp
	mov DWORD PTR [edi], ebx
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+24]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], ebx
	mov eax, DWORD PTR [edi+28]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+4]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+196]
	mov DWORD PTR [edi+196], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+8]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+200]
	mov DWORD PTR [edi+200], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+12]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+204]
	mov DWORD PTR [edi+204], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+16]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+208]
	mov DWORD PTR [edi+208], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+20]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+212]
	mov DWORD PTR [edi+212], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+24]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+216]
	mov DWORD PTR [edi+216], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+28]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+220]
	mov DWORD PTR [edi+220], ebx
	mov eax, DWORD PTR [edi+128]
	xor eax, DWORD PTR [edi+160]
	xor eax, DWORD PTR [edi+192]
	xor eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+132]
	xor eax, DWORD PTR [edi+164]
	xor eax, DWORD PTR [edi+196]
	xor eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+136]
	xor eax, DWORD PTR [edi+168]
	xor eax, DWORD PTR [edi+200]
	xor eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+140]
	xor eax, DWORD PTR [edi+172]
	xor eax, DWORD PTR [edi+204]
	xor eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+144]
	xor eax, DWORD PTR [edi+176]
	xor eax, DWORD PTR [edi+208]
	xor eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+148]
	xor eax, DWORD PTR [edi+180]
	xor eax, DWORD PTR [edi+212]
	xor eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+152]
	xor eax, DWORD PTR [edi+184]
	xor eax, DWORD PTR [edi+216]
	xor eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+156]
	xor eax, DWORD PTR [edi+188]
	xor eax, DWORD PTR [edi+220]
	xor eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	xor ecx, ebx
	mov edx, DWORD PTR [edi+28]
	xor edx, eax
	mov ebp, DWORD PTR [edi+20]
	xor ebp, ecx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ebp
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+12]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+24]
	xor edx, ecx
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	xor ebp, DWORD PTR [edi+4]
	xor ebp, -1
	mov DWORD PTR [edi+60], ebp
	mov ebp, ebx
	xor ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi]
	xor ebx, edx
	xor edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+68], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+24]
	mov DWORD PTR [edi+72], edx
	mov edx, DWORD PTR [edi]
	xor edx, DWORD PTR [edi+44]
	xor edx, -1
	mov DWORD PTR [edi+76], edx
	mov edx, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+80], edx
	mov edx, DWORD PTR [edi+12]
	xor edx, ecx
	xor edx, -1
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+32]
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+40]
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+40]
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+8]
	xor ebp, -1
	xor ebx, DWORD PTR [edi+4]
	xor ebx, -1
	xor ecx, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], ebx
	mov ebx, DWORD PTR [edi+20]
	xor ebx, DWORD PTR [edi+52]
	xor ebx, -1
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+4]
	xor ebp, DWORD PTR [edi+48]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+28]
	xor eax, DWORD PTR [edi+32]
	xor eax, -1
	mov DWORD PTR [edi+32], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+100], ebp
	mov ebp, DWORD PTR [edi+40]
	and ebp, edx
	xor ebp, eax
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+84]
	and edx, DWORD PTR [edi+80]
	xor edx, eax
	mov eax, DWORD PTR [edi+4]
	and eax, ecx
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+36]
	and ecx, ebx
	xor ecx, eax
	mov DWORD PTR [edi+112], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+76]
	xor ebx, eax
	mov eax, DWORD PTR [edi+56]
	and eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+116], ebx
	mov ebx, DWORD PTR [edi+48]
	and ebx, DWORD PTR [edi+32]
	xor ebx, eax
	mov DWORD PTR [edi+120], ecx
	mov ecx, DWORD PTR [edi+92]
	and ecx, DWORD PTR [edi+44]
	xor ecx, eax
	xor ebp, ebx
	xor edx, ecx
	xor ebx, DWORD PTR [edi+120]
	xor ecx, DWORD PTR [edi+116]
	xor ebp, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+68]
	xor ebx, DWORD PTR [edi+88]
	xor ecx, DWORD PTR [edi+64]
	mov eax, ebp
	xor eax, edx
	and ebp, ebx
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	xor ebx, ebp
	mov DWORD PTR [edi+88], ebp
	mov ebp, eax
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+64]
	xor eax, ecx
	xor edx, DWORD PTR [edi+88]
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [edi+64]
	xor eax, edx
	mov DWORD PTR [edi+64], ebp
	mov ebp, ebx
	xor ebp, edx
	and ecx, ebp
	xor eax, ecx
	xor ebx, ecx
	and ebx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+68]
	mov ecx, ebx
	xor ecx, eax
	mov ebp, DWORD PTR [edi+64]
	xor ebp, edx
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+64]
	xor ebp, ebx
	mov DWORD PTR [edi+88], ebx
	mov ebx, edx
	xor ebx, eax
	mov DWORD PTR [edi+52], ebp
	mov ebp, DWORD PTR [edi+68]
	xor ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [edi+60]
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	and ecx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ecx
	mov ecx, edx
	and ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], ecx
	mov ecx, DWORD PTR [edi+88]
	and ecx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, ebp
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+116]
	and ecx, DWORD PTR [edi+44]
	and ebx, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], edx
	mov edx, DWORD PTR [edi+52]
	and edx, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], edx
	mov edx, DWORD PTR [edi+88]
	and edx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+68]
	and ecx, DWORD PTR [edi+56]
	and ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+116]
	and ebp, DWORD PTR [edi+92]
	xor ebx, ecx
	mov DWORD PTR [edi+92], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+60]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+76], eax
	mov eax, edx
	xor eax, ecx
	xor eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+36]
	mov DWORD PTR [edi+36], edx
	mov edx, DWORD PTR [edi+32]
	xor edx, eax
	xor ebp, ebx
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+56], ebx
	mov ebx, edx
	xor ebx, ebp
	mov DWORD PTR [edi+68], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, eax
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+48]
	xor edx, ecx
	xor edx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+108]
	xor ebx, DWORD PTR [edi+76]
	xor ebx, edx
	xor ebp, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+52]
	xor edx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+72]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, DWORD PTR [edi+116]
	xor ecx, -1
	xor ebx, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], ecx
	mov ecx, DWORD PTR [edi+80]
	xor ecx, DWORD PTR [edi+64]
	xor ebx, DWORD PTR [edi+32]
	xor ebx, -1
	xor ebp, edx
	xor ebp, -1
	mov edx, DWORD PTR [edi+60]
	xor edx, DWORD PTR [edi+104]
	mov DWORD PTR [edi+104], ebp
	mov ebp, DWORD PTR [edi+108]
	xor ebp, DWORD PTR [edi+68]
	xor edx, DWORD PTR [edi+68]
	xor ecx, DWORD PTR [edi+56]
	xor ecx, -1
	xor ebp, DWORD PTR [edi+112]
	xor eax, DWORD PTR [edi+48]
	xor eax, -1
	mov DWORD PTR [edi+24], ecx
	mov DWORD PTR [edi+20], edx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+8], ebp
	mov DWORD PTR [edi], ebx
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+24]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], ebx
	mov eax, DWORD PTR [edi+28]
	ror eax, 8
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+4]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+228]
	mov DWORD PTR [edi+228], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+8]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+232]
	mov DWORD PTR [edi+232], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+12]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+236]
	mov DWORD PTR [edi+236], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+16]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+240]
	mov DWORD PTR [edi+240], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+20]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+244]
	mov DWORD PTR [edi+244], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+24]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+248]
	mov DWORD PTR [edi+248], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, eax
	ror ebx, 8
	xor ebx, eax
	mov ecx, eax
	ror ecx, 16
	xor ebx, ecx
	mov eax, DWORD PTR [edi+28]
	xor ebx, eax
	ror eax, 24
	xor ebx, eax
	xor ebx, DWORD PTR [edi+252]
	mov DWORD PTR [edi+252], ebx
	add esi, 128
	mov eax, esi
	sub eax, edi
	cmp eax, 1408
	jne 20b
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
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+368], eax
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
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+372], eax
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
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+156]
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
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+380], eax
	mov ebx, DWORD PTR [edi+1408]
	mov esi, DWORD PTR [edi+1412]
	mov ebp, DWORD PTR [edi+1420]
	mov edi, DWORD PTR [edi+1416]
	ret
	.p2align 6
