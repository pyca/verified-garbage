// The functions of `src/ed25519.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+284], eax
	mov esi, DWORD PTR [esp+16]
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
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+348], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+128], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+132], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+136], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+140], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+144], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+148], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+152], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+160], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+164], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+168], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+172], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+180], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+184], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov esi, 64
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+128]
	add eax, eax
	mov DWORD PTR [edi+32], eax
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 8
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 7
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 6
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 5
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 4
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 3
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 2
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 1
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	test esi, esi
	jne 20b
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
	ret
	.p2align 6

vg_ed25519_public_key:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	call {vg_sha512_finalize_scratch}
	mov eax, DWORD PTR [esp+192]
	and eax, -8
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+220]
	and eax, 1073741823
	or eax, 1073741824
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_base}
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed25519_scalar_reduce:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+188], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov esi, 64
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+128]
	add eax, eax
	mov DWORD PTR [edi+32], eax
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 8
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 7
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 6
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 5
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 4
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 3
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 2
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	mov ebx, DWORD PTR [edi+32]
	shr ebx, 1
	and ebx, 1
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, 2
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ecx, 0
	sub ecx, ebx
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
	test esi, esi
	jne 20b
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
	ret
	.p2align 6

vg_ed25519_scalar_base:
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
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, 0
	mov DWORD PTR [edi+740], eax
	mov eax, 0
	mov DWORD PTR [edi+744], eax
	mov eax, 0
	mov DWORD PTR [edi+748], eax
	mov eax, 0
	mov DWORD PTR [edi+752], eax
	mov eax, 0
	mov DWORD PTR [edi+756], eax
	mov eax, 0
	mov DWORD PTR [edi+760], eax
	mov eax, 0
	mov DWORD PTR [edi+764], eax
	mov eax, -133860783
	mov DWORD PTR [edi+64], eax
	mov eax, 92435371
	mov DWORD PTR [edi+68], eax
	mov eax, -2059538222
	mov DWORD PTR [edi+72], eax
	mov eax, -2097852509
	mov DWORD PTR [edi+76], eax
	mov eax, 897260486
	mov DWORD PTR [edi+80], eax
	mov eax, 962069898
	mov DWORD PTR [edi+84], eax
	mov eax, -1036166470
	mov DWORD PTR [edi+88], eax
	mov eax, 1587327241
	mov DWORD PTR [edi+92], eax
	mov eax, -2013978234
	mov DWORD PTR [edi+96], eax
	mov eax, -120142641
	mov DWORD PTR [edi+100], eax
	mov eax, 1980002921
	mov DWORD PTR [edi+104], eax
	mov eax, 164453974
	mov DWORD PTR [edi+108], eax
	mov eax, -148945550
	mov DWORD PTR [edi+112], eax
	mov eax, 886758072
	mov DWORD PTR [edi+116], eax
	mov eax, -1026307688
	mov DWORD PTR [edi+120], eax
	mov eax, 284972234
	mov DWORD PTR [edi+124], eax
	mov eax, 1
	mov DWORD PTR [edi+128], eax
	mov eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, -1354983357
	mov DWORD PTR [edi+160], eax
	mov eax, -1698235031
	mov DWORD PTR [edi+164], eax
	mov eax, -1070249436
	mov DWORD PTR [edi+168], eax
	mov eax, -115030791
	mov DWORD PTR [edi+172], eax
	mov eax, 32601596
	mov DWORD PTR [edi+176], eax
	mov eax, -501196079
	mov DWORD PTR [edi+180], eax
	mov eax, 1979154672
	mov DWORD PTR [edi+184], eax
	mov eax, 1947723929
	mov DWORD PTR [edi+188], eax
	mov eax, -133860783
	mov DWORD PTR [edi+608], eax
	mov eax, 92435371
	mov DWORD PTR [edi+612], eax
	mov eax, -2059538222
	mov DWORD PTR [edi+616], eax
	mov eax, -2097852509
	mov DWORD PTR [edi+620], eax
	mov eax, 897260486
	mov DWORD PTR [edi+624], eax
	mov eax, 962069898
	mov DWORD PTR [edi+628], eax
	mov eax, -1036166470
	mov DWORD PTR [edi+632], eax
	mov eax, 1587327241
	mov DWORD PTR [edi+636], eax
	mov eax, -2013978234
	mov DWORD PTR [edi+640], eax
	mov eax, -120142641
	mov DWORD PTR [edi+644], eax
	mov eax, 1980002921
	mov DWORD PTR [edi+648], eax
	mov eax, 164453974
	mov DWORD PTR [edi+652], eax
	mov eax, -148945550
	mov DWORD PTR [edi+656], eax
	mov eax, 886758072
	mov DWORD PTR [edi+660], eax
	mov eax, -1026307688
	mov DWORD PTR [edi+664], eax
	mov eax, 284972234
	mov DWORD PTR [edi+668], eax
	mov eax, 1
	mov DWORD PTR [edi+672], eax
	mov eax, 0
	mov DWORD PTR [edi+676], eax
	mov eax, 0
	mov DWORD PTR [edi+680], eax
	mov eax, 0
	mov DWORD PTR [edi+684], eax
	mov eax, 0
	mov DWORD PTR [edi+688], eax
	mov eax, 0
	mov DWORD PTR [edi+692], eax
	mov eax, 0
	mov DWORD PTR [edi+696], eax
	mov eax, 0
	mov DWORD PTR [edi+700], eax
	mov eax, -1354983357
	mov DWORD PTR [edi+704], eax
	mov eax, -1698235031
	mov DWORD PTR [edi+708], eax
	mov eax, -1070249436
	mov DWORD PTR [edi+712], eax
	mov eax, -115030791
	mov DWORD PTR [edi+716], eax
	mov eax, 32601596
	mov DWORD PTR [edi+720], eax
	mov eax, -501196079
	mov DWORD PTR [edi+724], eax
	mov eax, 1979154672
	mov DWORD PTR [edi+728], eax
	mov eax, 1947723929
	mov DWORD PTR [edi+732], eax
	mov esi, 0
21:
	mov edx, esi
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edi
	movzx eax, BYTE PTR [edx+7175]
	add eax, eax
	movzx ecx, BYTE PTR [edx+7174]
	add eax, ecx
	add eax, eax
	movzx ecx, BYTE PTR [edx+7173]
	add eax, ecx
	add eax, eax
	movzx ecx, BYTE PTR [edx+7172]
	add eax, ecx
	sub eax, 8
	sbb ecx, ecx
	mov DWORD PTR [edi+1152], ecx
	xor eax, ecx
	sub eax, ecx
	mov ecx, eax
	xor ecx, 0
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1024], ecx
	mov ecx, eax
	xor ecx, 1
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1028], ecx
	mov ecx, eax
	xor ecx, 2
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1032], ecx
	mov ecx, eax
	xor ecx, 3
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1036], ecx
	mov ecx, eax
	xor ecx, 4
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1040], ecx
	mov ecx, eax
	xor ecx, 5
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1044], ecx
	mov ecx, eax
	xor ecx, 6
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1048], ecx
	mov ecx, eax
	xor ecx, 7
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1052], ecx
	mov ecx, eax
	xor ecx, 8
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1056], ecx
	movzx eax, BYTE PTR [edx+7171]
	add eax, eax
	movzx ecx, BYTE PTR [edx+7170]
	add eax, ecx
	add eax, eax
	movzx ecx, BYTE PTR [edx+7169]
	add eax, ecx
	add eax, eax
	movzx ecx, BYTE PTR [edx+7168]
	add eax, ecx
	sub eax, 8
	sbb ecx, ecx
	mov DWORD PTR [edi+1156], ecx
	xor eax, ecx
	sub eax, ecx
	mov ecx, eax
	xor ecx, 0
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1088], ecx
	mov ecx, eax
	xor ecx, 1
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1092], ecx
	mov ecx, eax
	xor ecx, 2
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1096], ecx
	mov ecx, eax
	xor ecx, 3
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1100], ecx
	mov ecx, eax
	xor ecx, 4
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1104], ecx
	mov ecx, eax
	xor ecx, 5
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1108], ecx
	mov ecx, eax
	xor ecx, 6
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1112], ecx
	mov ecx, eax
	xor ecx, 7
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1116], ecx
	mov ecx, eax
	xor ecx, 8
	sub ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+1120], ecx
	mov eax, esi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [edi+1160]
	add ecx, eax
	add ecx, eax
	add ecx, eax
	mov ebx, DWORD PTR [edi+1024]
	and ebx, 1
	mov ebp, DWORD PTR [edi+1088]
	and ebp, 1
	mov eax, DWORD PTR [ecx]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+32]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+64]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+96]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+128]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+160]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+192]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+224]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+192], ebx
	mov DWORD PTR [edi+480], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+4]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+36]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+68]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+100]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+132]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+164]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+196]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+228]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+196], ebx
	mov DWORD PTR [edi+484], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+8]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+40]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+72]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+104]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+136]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+168]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+200]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+232]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+200], ebx
	mov DWORD PTR [edi+488], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+12]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+44]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+76]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+108]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+140]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+172]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+204]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+236]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+204], ebx
	mov DWORD PTR [edi+492], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+16]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+48]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+80]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+112]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+144]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+176]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+208]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+240]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+208], ebx
	mov DWORD PTR [edi+496], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+20]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+52]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+84]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+116]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+148]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+180]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+212]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+244]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+212], ebx
	mov DWORD PTR [edi+500], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+24]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+56]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+88]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+120]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+152]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+184]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+216]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+248]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+216], ebx
	mov DWORD PTR [edi+504], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+28]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+60]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+92]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+124]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+156]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+188]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+220]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+252]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+220], ebx
	mov DWORD PTR [edi+508], ebp
	mov ebx, DWORD PTR [edi+1024]
	and ebx, 1
	mov ebp, DWORD PTR [edi+1088]
	and ebp, 1
	mov eax, DWORD PTR [ecx+256]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+288]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+320]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+352]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+384]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+416]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+448]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+480]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+224], ebx
	mov DWORD PTR [edi+512], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+260]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+292]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+324]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+356]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+388]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+420]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+452]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+484]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+228], ebx
	mov DWORD PTR [edi+516], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+264]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+296]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+328]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+360]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+392]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+424]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+456]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+488]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+232], ebx
	mov DWORD PTR [edi+520], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+268]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+300]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+332]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+364]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+396]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+428]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+460]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+492]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+236], ebx
	mov DWORD PTR [edi+524], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+272]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+304]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+336]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+368]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+400]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+432]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+464]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+496]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+240], ebx
	mov DWORD PTR [edi+528], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+276]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+308]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+340]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+372]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+404]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+436]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+468]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+500]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+244], ebx
	mov DWORD PTR [edi+532], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+280]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+312]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+344]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+376]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+408]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+440]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+472]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+504]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+248], ebx
	mov DWORD PTR [edi+536], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+284]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+316]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+348]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+380]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+412]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+444]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+476]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+508]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+252], ebx
	mov DWORD PTR [edi+540], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+512]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+544]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+576]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+608]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+640]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+672]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+704]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+736]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+256], ebx
	mov DWORD PTR [edi+544], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+516]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+548]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+580]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+612]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+644]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+676]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+708]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+740]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+260], ebx
	mov DWORD PTR [edi+548], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+520]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+552]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+584]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+616]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+648]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+680]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+712]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+744]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+264], ebx
	mov DWORD PTR [edi+552], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+524]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+556]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+588]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+620]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+652]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+684]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+716]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+748]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+268], ebx
	mov DWORD PTR [edi+556], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+528]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+560]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+592]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+624]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+656]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+688]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+720]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+752]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+272], ebx
	mov DWORD PTR [edi+560], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+532]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+564]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+596]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+628]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+660]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+692]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+724]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+756]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+276], ebx
	mov DWORD PTR [edi+564], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+536]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+568]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+600]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+632]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+664]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+696]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+728]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+760]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+280], ebx
	mov DWORD PTR [edi+568], ebp
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [ecx+540]
	mov edx, eax
	and eax, DWORD PTR [edi+1028]
	and edx, DWORD PTR [edi+1092]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+572]
	mov edx, eax
	and eax, DWORD PTR [edi+1032]
	and edx, DWORD PTR [edi+1096]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+604]
	mov edx, eax
	and eax, DWORD PTR [edi+1036]
	and edx, DWORD PTR [edi+1100]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+636]
	mov edx, eax
	and eax, DWORD PTR [edi+1040]
	and edx, DWORD PTR [edi+1104]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+668]
	mov edx, eax
	and eax, DWORD PTR [edi+1044]
	and edx, DWORD PTR [edi+1108]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+700]
	mov edx, eax
	and eax, DWORD PTR [edi+1048]
	and edx, DWORD PTR [edi+1112]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+732]
	mov edx, eax
	and eax, DWORD PTR [edi+1052]
	and edx, DWORD PTR [edi+1116]
	or ebx, eax
	or ebp, edx
	mov eax, DWORD PTR [ecx+764]
	mov edx, eax
	and eax, DWORD PTR [edi+1056]
	and edx, DWORD PTR [edi+1120]
	or ebx, eax
	or ebp, edx
	mov DWORD PTR [edi+284], ebx
	mov DWORD PTR [edi+572], ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+544]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	mov ecx, DWORD PTR [edi+1156]
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+512]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+480], eax
	mov DWORD PTR [edi+512], edx
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+516]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+484], eax
	mov DWORD PTR [edi+516], edx
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+520]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+488], eax
	mov DWORD PTR [edi+520], edx
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+524]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+492], eax
	mov DWORD PTR [edi+524], edx
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+528]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+496], eax
	mov DWORD PTR [edi+528], edx
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+532]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+500], eax
	mov DWORD PTR [edi+532], edx
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+536]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+504], eax
	mov DWORD PTR [edi+536], edx
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+540]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+508], eax
	mov DWORD PTR [edi+540], edx
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+320]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+544], eax
	mov DWORD PTR [edi+320], edx
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+324]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+548], eax
	mov DWORD PTR [edi+324], edx
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+328]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+552], eax
	mov DWORD PTR [edi+328], edx
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+332]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+556], eax
	mov DWORD PTR [edi+332], edx
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+336]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+560], eax
	mov DWORD PTR [edi+336], edx
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+340]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+564], eax
	mov DWORD PTR [edi+340], edx
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+344]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+568], eax
	mov DWORD PTR [edi+344], edx
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+348]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+572], eax
	mov DWORD PTR [edi+348], edx
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+640]
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
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+644]
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
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+648]
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
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+652]
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
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+656]
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
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+660]
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
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+664]
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
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+668]
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
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
	add ebx, DWORD PTR [edi+640]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+608]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+644]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+612]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+648]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+616]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+652]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+620]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+656]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+624]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+660]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+628]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+664]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+632]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+668]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+636]
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
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+380]
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+732]
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
	add ebx, DWORD PTR [edi+672]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+416], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+676]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+676]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+420], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+680]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+680]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+424], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+684]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+684]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+428], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+688]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+688]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+432], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+692]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+692]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+436], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+696]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+696]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+440], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+700]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+700]
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
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+348]
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
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+320]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+352], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+356], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+360], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+364], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+368], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+372], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+376], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+412]
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
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+384]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+384], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+388], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+392], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+396], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+400], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+404], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+408], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
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
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+380]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+380]
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
	mov DWORD PTR [edi+640], ebx
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
	mov DWORD PTR [edi+644], ebx
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
	mov DWORD PTR [edi+648], ebx
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
	mov DWORD PTR [edi+652], ebx
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
	mov DWORD PTR [edi+656], ebx
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
	mov DWORD PTR [edi+660], ebx
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
	mov DWORD PTR [edi+664], ebx
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
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+412]
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
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
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+256]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+320], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+324], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+328], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+332], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+336], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+340], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+344], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	mov ecx, DWORD PTR [edi+1152]
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+224]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+224], edx
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+228]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+228], edx
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+232]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+232], edx
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+236]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+236], edx
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+240]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+208], eax
	mov DWORD PTR [edi+240], edx
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+244]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+212], eax
	mov DWORD PTR [edi+244], edx
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+248]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+216], eax
	mov DWORD PTR [edi+248], edx
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+252]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+220], eax
	mov DWORD PTR [edi+252], edx
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+320]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+256], eax
	mov DWORD PTR [edi+320], edx
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+324]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+260], eax
	mov DWORD PTR [edi+324], edx
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+328]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+264], eax
	mov DWORD PTR [edi+328], edx
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+332]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+268], eax
	mov DWORD PTR [edi+332], edx
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+336]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+272], eax
	mov DWORD PTR [edi+336], edx
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+340]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+276], eax
	mov DWORD PTR [edi+340], edx
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+344]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+280], eax
	mov DWORD PTR [edi+344], edx
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+348]
	mov ebx, eax
	xor ebx, edx
	and ebx, ecx
	xor eax, ebx
	xor edx, ebx
	mov DWORD PTR [edi+284], eax
	mov DWORD PTR [edi+348], edx
	push edi
	call {vg_ed25519_r32_add_affine}
	pop eax
	add esi, 1
	cmp esi, 32
	jne 21b
	mov esi, 4
22:
	push edi
	call {vg_ed25519_r32_double}
	pop eax
	sub esi, 1
	jne 22b
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
	push edi
	call {vg_gf25519_r32_pow250}
	pop eax
	mov esi, 5
23:
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
	jne 23b
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
	mov DWORD PTR [edi+64], ebx
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
	mov DWORD PTR [edi+68], ebx
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
	mov DWORD PTR [edi+72], ebx
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
	mov DWORD PTR [edi+76], ebx
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
	mov DWORD PTR [edi+80], ebx
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
	mov DWORD PTR [edi+84], ebx
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
	mov DWORD PTR [edi+88], ebx
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
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+544]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+548]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+552]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+556]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+560]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+564]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+572]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+568]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+124]
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
	mov DWORD PTR [edi+96], ebx
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
	mov DWORD PTR [edi+100], ebx
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
	mov DWORD PTR [edi+104], ebx
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
	mov DWORD PTR [edi+108], ebx
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
	mov DWORD PTR [edi+112], ebx
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
	mov DWORD PTR [edi+116], ebx
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
	mov DWORD PTR [edi+120], ebx
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
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+96], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+100], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+104], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+108], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+112], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+116], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+120], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
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
	mov esi, DWORD PTR [edi+64]
	and esi, 1
	ror esi, 1
	mov eax, DWORD PTR [edi+124]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+124]
	and eax, 2147483647
	mov DWORD PTR [edi+124], eax
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+96], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+100], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+104], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+108], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+112], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+116], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+120], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+124]
	add eax, esi
	mov DWORD PTR [edi+124], eax
	mov esi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [esi+28], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	ret
	.p2align 6

vg_ed25519_sign_cached:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	call {vg_sha512_finalize_scratch}
	mov eax, DWORD PTR [esp+192]
	and eax, -8
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+220]
	and eax, 1073741823
	or eax, 1073741824
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 64
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	mov edx, 0
	add eax, 32
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_base}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	mov edx, 0
	add eax, 64
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
	mov eax, DWORD PTR [esp+260]
	add eax, 32
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+280]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	call {vg_ed25519_scalar_mul_add}
	mov eax, 0
	mov DWORD PTR [esp+32], eax
	mov eax, 0
	mov DWORD PTR [esp+36], eax
	mov eax, 0
	mov DWORD PTR [esp+40], eax
	mov eax, 0
	mov DWORD PTR [esp+44], eax
	mov eax, 0
	mov DWORD PTR [esp+48], eax
	mov eax, 0
	mov DWORD PTR [esp+52], eax
	mov eax, 0
	mov DWORD PTR [esp+56], eax
	mov eax, 0
	mov DWORD PTR [esp+60], eax
	mov eax, 0
	mov DWORD PTR [esp+64], eax
	mov eax, 0
	mov DWORD PTR [esp+68], eax
	mov eax, 0
	mov DWORD PTR [esp+72], eax
	mov eax, 0
	mov DWORD PTR [esp+76], eax
	mov eax, 0
	mov DWORD PTR [esp+80], eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+88], eax
	mov eax, 0
	mov DWORD PTR [esp+92], eax
	mov eax, 0
	mov DWORD PTR [esp+96], eax
	mov eax, 0
	mov DWORD PTR [esp+100], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov eax, 0
	mov DWORD PTR [esp+108], eax
	mov eax, 0
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov eax, 0
	mov DWORD PTR [esp+120], eax
	mov eax, 0
	mov DWORD PTR [esp+124], eax
	mov eax, 0
	mov DWORD PTR [esp+128], eax
	mov eax, 0
	mov DWORD PTR [esp+132], eax
	mov eax, 0
	mov DWORD PTR [esp+136], eax
	mov eax, 0
	mov DWORD PTR [esp+140], eax
	mov eax, 0
	mov DWORD PTR [esp+144], eax
	mov eax, 0
	mov DWORD PTR [esp+148], eax
	mov eax, 0
	mov DWORD PTR [esp+152], eax
	mov eax, 0
	mov DWORD PTR [esp+156], eax
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, 0
	mov DWORD PTR [esp+192], eax
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov eax, 0
	mov DWORD PTR [esp+200], eax
	mov eax, 0
	mov DWORD PTR [esp+204], eax
	mov eax, 0
	mov DWORD PTR [esp+208], eax
	mov eax, 0
	mov DWORD PTR [esp+212], eax
	mov eax, 0
	mov DWORD PTR [esp+216], eax
	mov eax, 0
	mov DWORD PTR [esp+220], eax
	mov eax, 0
	mov DWORD PTR [esp+224], eax
	mov eax, 0
	mov DWORD PTR [esp+228], eax
	mov eax, 0
	mov DWORD PTR [esp+232], eax
	mov eax, 0
	mov DWORD PTR [esp+236], eax
	mov eax, 0
	mov DWORD PTR [esp+240], eax
	mov eax, 0
	mov DWORD PTR [esp+244], eax
	mov eax, 0
	mov DWORD PTR [esp+248], eax
	mov eax, 0
	mov DWORD PTR [esp+252], eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_ed25519_verify_equation:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	add esi, 32
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+92], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+64]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1559614445
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+68]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1477600027
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+72]
	adc ecx, 0
	adc ebp, 0
	add ebx, 1560830761
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+76]
	adc ecx, 0
	adc ebp, 0
	add ebx, -350157279
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+80]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+84]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+88]
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+92]
	adc ecx, 0
	adc ebp, 0
	add ebx, -268435457
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	test ebx, ebx
	je 20f
	mov eax, 0
	jmp 21f
20:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [edi+7936], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+7940], eax
	mov eax, 7680
	mov DWORD PTR [edi+7944], eax
	mov eax, 1
	mov DWORD PTR [edi+7948], eax
22:
	mov esi, DWORD PTR [edi+7936]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+124], eax
	mov esi, DWORD PTR [edi+124]
	shr esi, 31
	mov DWORD PTR [edi+32], esi
	mov eax, DWORD PTR [edi+124]
	and eax, 2147483647
	mov DWORD PTR [edi+124], eax
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+892]
	shr eax, 31
	test eax, eax
	je 23f
	mov eax, 0
	jmp 24f
23:
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
	mov eax, 1
	mov DWORD PTR [edi+192], eax
	mov eax, 0
	mov DWORD PTR [edi+196], eax
	mov eax, 0
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
	mov eax, 0
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 0
	mov DWORD PTR [edi+216], eax
	mov eax, 0
	mov DWORD PTR [edi+220], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+100]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+104]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+108]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+112]
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
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+116]
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
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+120]
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
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+124]
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
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+124]
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
	mov DWORD PTR [edi+224], ebx
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
	mov DWORD PTR [edi+228], ebx
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
	mov DWORD PTR [edi+232], ebx
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
	mov DWORD PTR [edi+236], ebx
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
	mov DWORD PTR [edi+240], ebx
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
	mov DWORD PTR [edi+244], ebx
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
	mov DWORD PTR [edi+248], ebx
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
	mov DWORD PTR [edi+252], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+224]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+224], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+228]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+228], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+232]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+232], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+236]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+236], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+240]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+240], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+244]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+244], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+248]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+248], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+252]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+252], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+224], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+224]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+256], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+228]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+260], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+232]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+264], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+236]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+268], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+240]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+272], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+244]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+276], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+248]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+280], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+252]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+284], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+256]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+256], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+260]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+260], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+264]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+264], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+268]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+268], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+272]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+272], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+276]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+276], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+280]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+280], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+284]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+284], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+256], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+124]
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
	mov DWORD PTR [edi+288], ebx
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
	mov DWORD PTR [edi+292], ebx
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
	mov DWORD PTR [edi+296], ebx
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
	mov DWORD PTR [edi+300], ebx
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
	mov DWORD PTR [edi+304], ebx
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
	mov DWORD PTR [edi+308], ebx
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
	mov DWORD PTR [edi+312], ebx
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
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+288]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+292]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+296]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+300]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+304]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+308]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+312]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+316]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+288], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+124]
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
	mov DWORD PTR [edi+288], ebx
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
	mov DWORD PTR [edi+292], ebx
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
	mov DWORD PTR [edi+296], ebx
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
	mov DWORD PTR [edi+300], ebx
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
	mov DWORD PTR [edi+304], ebx
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
	mov DWORD PTR [edi+308], ebx
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
	mov DWORD PTR [edi+312], ebx
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
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+288]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+292]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+296]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+300]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+304]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+308]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+312]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+316]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+288], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+288]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+192]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+292]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+196]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+296]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+200]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+300]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+204]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+304]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+208]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+308]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+212]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+312]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+216]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+316]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+220]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+288]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+292]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+296]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+300]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+304]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+308]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+312]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+316]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+288], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+292]
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
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+296]
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
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+300]
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
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+304]
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
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+308]
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
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+312]
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
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+316]
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
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+316]
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
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+320]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+324]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+328]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+332]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+336]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+340]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+344]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+348]
	mov edx, DWORD PTR [edi+316]
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+356]
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
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+360]
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
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+364]
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
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+352]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+368]
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
	mov eax, DWORD PTR [edi+356]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+360]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+372]
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
	mov eax, DWORD PTR [edi+364]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+368]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+376]
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
	mov eax, DWORD PTR [edi+372]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+376]
	mov edx, DWORD PTR [edi+380]
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
	mov eax, DWORD PTR [edi+380]
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
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+384]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+288]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+388]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+292]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+392]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+296]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+396]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+300]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+400]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+304]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+404]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+308]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+408]
	mov edx, DWORD PTR [edi+316]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+312]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+412]
	mov edx, DWORD PTR [edi+316]
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
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+384]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+388]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+392]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+396]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+400]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+404]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+412]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+408]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+284]
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
	mov DWORD PTR [edi+128], ebx
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
	mov DWORD PTR [edi+132], ebx
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
	mov DWORD PTR [edi+136], ebx
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
	mov DWORD PTR [edi+140], ebx
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
	mov DWORD PTR [edi+144], ebx
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
	mov DWORD PTR [edi+148], ebx
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
	mov DWORD PTR [edi+152], ebx
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
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+128]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+128], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+132]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+132], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+136]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+136], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+140]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+140], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+144]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+144], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+148]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+148], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+152]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+152], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+156]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+128], eax
	push edi
	call {vg_gf25519_r32_pow250}
	pop eax
	mov esi, 2
25:
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
	jne 25b
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+544]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+548]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+552]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+556]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+560]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+564]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+156]
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
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+224]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+256]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+228]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+232]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+236]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+240]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+244]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+248]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+252]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+256]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+352]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+260]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+356]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+360]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+364]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+368]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+372]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+380]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+376]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+284]
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
	mov DWORD PTR [edi+64], ebx
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
	mov DWORD PTR [edi+68], ebx
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
	mov DWORD PTR [edi+72], ebx
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
	mov DWORD PTR [edi+76], ebx
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
	mov DWORD PTR [edi+80], ebx
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
	mov DWORD PTR [edi+84], ebx
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
	mov DWORD PTR [edi+88], ebx
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
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
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
	mov DWORD PTR [edi+64], ebx
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
	mov DWORD PTR [edi+68], ebx
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
	mov DWORD PTR [edi+72], ebx
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
	mov DWORD PTR [edi+76], ebx
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
	mov DWORD PTR [edi+80], ebx
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
	mov DWORD PTR [edi+84], ebx
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
	mov DWORD PTR [edi+88], ebx
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
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+304]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+308]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+312]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+316]
	mov edx, DWORD PTR [edi+92]
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
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+92]
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
	mov esi, DWORD PTR [edi+32]
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+256]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+260]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+264]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+268]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+272]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+276]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+280]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+284]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+764]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+764]
	and eax, 2147483647
	mov DWORD PTR [edi+764], eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
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
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov edx, DWORD PTR [edi+736]
	or eax, edx
	mov edx, DWORD PTR [edi+740]
	or eax, edx
	mov edx, DWORD PTR [edi+744]
	or eax, edx
	mov edx, DWORD PTR [edi+748]
	or eax, edx
	mov edx, DWORD PTR [edi+752]
	or eax, edx
	mov edx, DWORD PTR [edi+756]
	or eax, edx
	mov edx, DWORD PTR [edi+760]
	or eax, edx
	mov edx, DWORD PTR [edi+764]
	or eax, edx
	test eax, eax
	je 26f
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+448]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+420]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+424]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+428]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+432]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+436]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+440]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+444]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+764]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+764]
	and eax, 2147483647
	mov DWORD PTR [edi+764], eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
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
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov edx, DWORD PTR [edi+736]
	or eax, edx
	mov edx, DWORD PTR [edi+740]
	or eax, edx
	mov edx, DWORD PTR [edi+744]
	or eax, edx
	mov edx, DWORD PTR [edi+748]
	or eax, edx
	mov edx, DWORD PTR [edi+752]
	or eax, edx
	mov edx, DWORD PTR [edi+756]
	or eax, edx
	mov edx, DWORD PTR [edi+760]
	or eax, edx
	mov edx, DWORD PTR [edi+764]
	or eax, edx
	test eax, eax
	je 28f
	mov eax, 0
	jmp 29f
28:
	mov eax, 1242472624
	mov DWORD PTR [edi+640], eax
	mov eax, -991028441
	mov DWORD PTR [edi+644], eax
	mov eax, -1389370248
	mov DWORD PTR [edi+648], eax
	mov eax, 792926214
	mov DWORD PTR [edi+652], eax
	mov eax, 1039914919
	mov DWORD PTR [edi+656], eax
	mov eax, 726466713
	mov DWORD PTR [edi+660], eax
	mov eax, 1338105611
	mov DWORD PTR [edi+664], eax
	mov eax, 730014848
	mov DWORD PTR [edi+668], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+668]
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
	mov DWORD PTR [edi+64], ebx
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
	mov DWORD PTR [edi+68], ebx
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
	mov DWORD PTR [edi+72], ebx
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
	mov DWORD PTR [edi+76], ebx
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
	mov DWORD PTR [edi+80], ebx
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
	mov DWORD PTR [edi+84], ebx
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
	mov DWORD PTR [edi+88], ebx
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
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	mov eax, 1
29:
	jmp 27f
26:
	mov eax, 1
27:
	test eax, eax
	jne 210f
	mov eax, 0
	jmp 211f
210:
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
	mov eax, 0
	mov edx, DWORD PTR [edi+64]
	or eax, edx
	mov edx, DWORD PTR [edi+68]
	or eax, edx
	mov edx, DWORD PTR [edi+72]
	or eax, edx
	mov edx, DWORD PTR [edi+76]
	or eax, edx
	mov edx, DWORD PTR [edi+80]
	or eax, edx
	mov edx, DWORD PTR [edi+84]
	or eax, edx
	mov edx, DWORD PTR [edi+88]
	or eax, edx
	mov edx, DWORD PTR [edi+92]
	or eax, edx
	test eax, eax
	je 212f
	mov eax, 0
	jmp 213f
212:
	mov eax, esi
213:
	test eax, eax
	jne 214f
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
	mov eax, DWORD PTR [edi+64]
	and eax, 1
	xor eax, esi
	test eax, eax
	je 216f
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+224]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+64]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+64], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+228]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+68], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+232]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+72], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+236]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+76], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+240]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+80], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+244]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+84], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+248]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+88], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+252]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	jmp 217f
216:
217:
	mov eax, 1
	mov DWORD PTR [edi+128], eax
	mov eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+124]
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
	mov DWORD PTR [edi+160], ebx
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
	mov DWORD PTR [edi+164], ebx
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
	mov DWORD PTR [edi+168], ebx
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
	mov DWORD PTR [edi+172], ebx
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
	mov DWORD PTR [edi+176], ebx
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
	mov DWORD PTR [edi+180], ebx
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
	mov DWORD PTR [edi+184], ebx
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
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+160]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+160], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+164]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+164], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+168]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+168], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+172]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+172], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+176]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+180]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+180], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+184]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+184], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+188]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	mov eax, 1
	jmp 215f
214:
	mov eax, 0
215:
211:
24:
	mov ecx, eax
	mov edx, DWORD PTR [edi+7944]
	add edx, edi
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edx+124], eax
	mov edx, DWORD PTR [edi+7948]
	and edx, ecx
	mov DWORD PTR [edi+7948], edx
	mov eax, DWORD PTR [edi+7940]
	mov DWORD PTR [edi+7936], eax
	mov edx, DWORD PTR [edi+7944]
	add edx, 128
	mov DWORD PTR [edi+7944], edx
	cmp edx, 7936
	jne 22b
	mov eax, DWORD PTR [edi+7948]
	test eax, eax
	jne 218f
	mov eax, 0
	jmp 219f
218:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_ED25519_VERIFY_NEG_BASE}
	pop ecx
	mov esi, eax
	mov edx, edi
	add edx, 3072
	mov ecx, 480
220:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edx], eax
	add esi, 4
	add edx, 4
	sub ecx, 1
	jne 220b
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
	mov edx, edi
	add edx, 7680
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edi+188], eax
	mov edx, edi
	add edx, 1024
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edx+124], eax
	mov esi, 1
221:
	mov edx, edi
	add edx, 7680
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edi+316], eax
	push edi
	call {vg_ed25519_r32_point_add}
	pop eax
	mov eax, esi
	mov edx, 128
	mul edx
	add eax, edi
	add eax, 1024
	mov edx, eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edx+124], eax
	add esi, 1
	cmp esi, 15
	jne 221b
	mov eax, 0
	mov DWORD PTR [edi+64], eax
	mov eax, 0
	mov DWORD PTR [edi+68], eax
	mov eax, 0
	mov DWORD PTR [edi+72], eax
	mov eax, 0
	mov DWORD PTR [edi+76], eax
	mov eax, 0
	mov DWORD PTR [edi+80], eax
	mov eax, 0
	mov DWORD PTR [edi+84], eax
	mov eax, 0
	mov DWORD PTR [edi+88], eax
	mov eax, 0
	mov DWORD PTR [edi+92], eax
	mov eax, 1
	mov DWORD PTR [edi+96], eax
	mov eax, 0
	mov DWORD PTR [edi+100], eax
	mov eax, 0
	mov DWORD PTR [edi+104], eax
	mov eax, 0
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, 0
	mov DWORD PTR [edi+116], eax
	mov eax, 0
	mov DWORD PTR [edi+120], eax
	mov eax, 0
	mov DWORD PTR [edi+124], eax
	mov eax, 1
	mov DWORD PTR [edi+128], eax
	mov eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, 0
	mov DWORD PTR [edi+160], eax
	mov eax, 0
	mov DWORD PTR [edi+164], eax
	mov eax, 0
	mov DWORD PTR [edi+168], eax
	mov eax, 0
	mov DWORD PTR [edi+172], eax
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov eax, 0
	mov DWORD PTR [edi+180], eax
	mov eax, 0
	mov DWORD PTR [edi+184], eax
	mov eax, 0
	mov DWORD PTR [edi+188], eax
	mov esi, 64
222:
	mov edx, esi
	sub edx, 1
	mov eax, DWORD PTR [esp+12]
	add eax, edx
	movzx eax, BYTE PTR [eax]
	test eax, eax
	jne 223f
	mov esi, edx
	cmp esi, 32
	jmp 224f
223:
	cmp esi, esi
224:
	jne 222b
	add esi, esi
225:
	sub esi, 1
226:
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+64]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+68]
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
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+68]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+72]
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
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+72]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+76]
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
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+76]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+80]
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
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+80]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+84]
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
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+84]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+88]
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
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+92]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+88]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+92]
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
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+92]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+100]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+104]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+108]
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
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+112]
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
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+116]
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
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+120]
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
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+124]
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
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+124]
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+132]
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
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+136]
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
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+140]
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
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+144]
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
	mov eax, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+148]
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
	mov eax, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+152]
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
	mov eax, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+156]
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
	mov eax, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+156]
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
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
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
	add ebx, DWORD PTR [edi+412]
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
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+96]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+100]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+104]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+108]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+112]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+116]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+124]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+120]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+124]
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
	add ebx, DWORD PTR [edi+416]
	adc ecx, 0
	adc ebp, 0
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
	add ebx, DWORD PTR [edi+444]
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
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+320]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+448], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+324]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+452], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+328]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+456], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+332]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+460], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+336]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+464], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+340]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+468], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+344]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+472], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+380]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+348]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
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
	add ebx, DWORD PTR [edi+384]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+448]
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
	add ebx, DWORD PTR [edi+388]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
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
	add ebx, DWORD PTR [edi+392]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
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
	add ebx, DWORD PTR [edi+396]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
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
	add ebx, DWORD PTR [edi+400]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
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
	add ebx, DWORD PTR [edi+404]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
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
	add ebx, DWORD PTR [edi+408]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
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
	add ebx, DWORD PTR [edi+412]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
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
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+352]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+512], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+356]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+516], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+360]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+520], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+364]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+524], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+368]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+528], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+372]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+532], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+376]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+536], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+380]
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
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+480]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+484]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+488]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+492]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+496]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+500]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+508]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+504]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
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
	mov DWORD PTR [edi+64], ebx
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
	mov DWORD PTR [edi+68], ebx
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
	mov DWORD PTR [edi+72], ebx
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
	mov DWORD PTR [edi+76], ebx
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
	mov DWORD PTR [edi+80], ebx
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
	mov DWORD PTR [edi+84], ebx
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
	mov DWORD PTR [edi+88], ebx
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
	mov DWORD PTR [edi+92], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
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
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+64], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+476]
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
	mov DWORD PTR [edi+96], ebx
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
	mov DWORD PTR [edi+100], ebx
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
	mov DWORD PTR [edi+104], ebx
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
	mov DWORD PTR [edi+108], ebx
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
	mov DWORD PTR [edi+112], ebx
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
	mov DWORD PTR [edi+116], ebx
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
	mov DWORD PTR [edi+120], ebx
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
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+96]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+96], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+100]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+100], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+104]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+104], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+108]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+108], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+112]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+112], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+116]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+116], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+120]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+120], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+124]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+124], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+96], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+448]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+452]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+456]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+460]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+464]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+468]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+476]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+472]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+508]
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
	mov DWORD PTR [edi+128], ebx
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
	mov DWORD PTR [edi+132], ebx
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
	mov DWORD PTR [edi+136], ebx
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
	mov DWORD PTR [edi+140], ebx
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
	mov DWORD PTR [edi+144], ebx
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
	mov DWORD PTR [edi+148], ebx
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
	mov DWORD PTR [edi+152], ebx
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
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+128]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+128], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+132]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+132], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+136]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+136], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+140]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+140], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+144]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+144], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+148]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+148], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+152]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+152], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+156]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+156], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+128], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+416]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+512]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+420]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+516]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+424]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+520]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+428]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+524]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+432]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+528]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+436]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+532]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+440]
	mov edx, DWORD PTR [edi+540]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+444]
	mov edx, DWORD PTR [edi+536]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+444]
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
	mov DWORD PTR [edi+160], ebx
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
	mov DWORD PTR [edi+164], ebx
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
	mov DWORD PTR [edi+168], ebx
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
	mov DWORD PTR [edi+172], ebx
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
	mov DWORD PTR [edi+176], ebx
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
	mov DWORD PTR [edi+180], ebx
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
	mov DWORD PTR [edi+184], ebx
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
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+160]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+160], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+164]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+164], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+168]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+168], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+172]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+172], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+176]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+176], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+180]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+180], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+184]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+184], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+188]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+188], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+160], eax
	add esi, 1073741824
	jae 226b
	mov eax, esi
	shr eax, 1
	add eax, DWORD PTR [esp+12]
	movzx eax, BYTE PTR [eax]
	test esi, 1
	jne 227f
	and eax, 15
	jmp 228f
227:
	shr eax, 4
228:
	test eax, eax
	jne 229f
	jmp 230f
229:
	sub eax, 1
	mov edx, 128
	mul edx
	add eax, edi
	add eax, 1024
	mov edx, eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edi+316], eax
	push edi
	call {vg_ed25519_r32_point_add}
	pop eax
230:
	cmp esi, 64
	jb 231f
	jmp 232f
231:
	mov eax, esi
	shr eax, 1
	add eax, DWORD PTR [esp+8]
	movzx eax, BYTE PTR [eax+32]
	test esi, 1
	jne 233f
	and eax, 15
	jmp 234f
233:
	shr eax, 4
234:
	test eax, eax
	jne 235f
	jmp 236f
235:
	sub eax, 1
	mov edx, 128
	mul edx
	add eax, edi
	add eax, 3072
	mov edx, eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edi+316], eax
	push edi
	call {vg_ed25519_r32_point_add}
	pop eax
236:
232:
	test esi, esi
	jne 225b
	mov edx, edi
	add edx, 7808
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edx+16]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edx+20]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edx+24]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edx+28]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edx+32]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edx+36]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edx+40]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edx+44]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edx+48]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edx+52]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edx+56]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edx+60]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edx+64]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edx+68]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edx+72]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edx+76]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edx+80]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edx+84]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edx+88]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edx+92]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edx+96]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edx+100]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edx+104]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edx+108]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edx+112]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edx+116]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edx+120]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edx+124]
	mov DWORD PTR [edi+316], eax
	mov eax, 0
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+192]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+192], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+196], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+200], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+204], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+208], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+212], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+216], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+220], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+192]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+192], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+196]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+196], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+200]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+200], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+204]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+204], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+208]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+208], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+212]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+212], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+216]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+216], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+220]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+220], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+192], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+320]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+288]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -75
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+324]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+292]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+328]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+296]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+332]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+300]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+336]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+304]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+340]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+308]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+344]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+312]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+348]
	adc ecx, 0
	adc ebp, 0
	mov eax, DWORD PTR [edi+316]
	xor eax, -1
	add ebx, eax
	adc ecx, 0
	adc ebp, 0
	add ebx, -1
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+288]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+288], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+292]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+292], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+296]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+296], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+300]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+300], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+304]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+304], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+308]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+308], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+312]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+312], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+316]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+316], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+288], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+284]
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
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+208]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+212]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+216]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+220]
	mov edx, DWORD PTR [edi+156]
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
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+256]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+260]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+264]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+268]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+272]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+276]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+284]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+280]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+284]
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
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+128]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+132]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+896], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+136]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+900], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+140]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+904], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+144]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+908], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+148]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+912], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+156]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+152]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+916], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+156]
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
	mov esi, 2
237:
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
	mov DWORD PTR [edi+736], ebx
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
	mov DWORD PTR [edi+740], ebx
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
	mov DWORD PTR [edi+744], ebx
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
	mov DWORD PTR [edi+748], ebx
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
	mov DWORD PTR [edi+752], ebx
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
	mov DWORD PTR [edi+756], ebx
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
	mov DWORD PTR [edi+760], ebx
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
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	mov ebx, eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, 38
	mul ebx
	add eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+764]
	shr eax, 31
	mov edx, 19
	mul edx
	mov ebx, eax
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+764]
	and eax, 2147483647
	mov DWORD PTR [edi+764], eax
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebx, 19
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+736]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+740]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+744]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+748]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+752]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+756]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+760]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+764]
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
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+888]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+892]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov edx, DWORD PTR [edi+736]
	or eax, edx
	mov edx, DWORD PTR [edi+740]
	or eax, edx
	mov edx, DWORD PTR [edi+744]
	or eax, edx
	mov edx, DWORD PTR [edi+748]
	or eax, edx
	mov edx, DWORD PTR [edi+752]
	or eax, edx
	mov edx, DWORD PTR [edi+756]
	or eax, edx
	mov edx, DWORD PTR [edi+760]
	or eax, edx
	mov edx, DWORD PTR [edi+764]
	or eax, edx
	test eax, eax
	je 238f
	mov eax, 0
	mov esi, 0
	test esi, esi
	jmp 239f
238:
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+380], eax
	mov eax, 1
	sub esi, 1
239:
	jne 237b
219:
21:
	mov edx, eax
	mov eax, edi
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov ebp, DWORD PTR [eax+12]
	mov edi, DWORD PTR [eax+8]
	mov eax, edx
	ret
	.p2align 6

vg_ed25519_verify:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	call {vg_sha512_init}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 32
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 64
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+264]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+268]
	add eax, 0
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+20], eax
	call {vg_sha512_update_scratch}
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 192
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+268]
	mov edx, 0
	add eax, 64
	adc edx, 0
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp+8], edx
	call {vg_sha512_finalize_scratch}
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp], eax
	mov eax, esp
	add eax, 192
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+8], eax
	call {vg_ed25519_scalar_reduce}
	mov eax, 0
	mov DWORD PTR [esp+160], eax
	mov eax, 0
	mov DWORD PTR [esp+164], eax
	mov eax, 0
	mov DWORD PTR [esp+168], eax
	mov eax, 0
	mov DWORD PTR [esp+172], eax
	mov eax, 0
	mov DWORD PTR [esp+176], eax
	mov eax, 0
	mov DWORD PTR [esp+180], eax
	mov eax, 0
	mov DWORD PTR [esp+184], eax
	mov eax, 0
	mov DWORD PTR [esp+188], eax
	mov eax, DWORD PTR [esp+260]
	add eax, 0
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+272]
	add eax, 0
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 128
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+276]
	add eax, 0
	mov DWORD PTR [esp+12], eax
	call {vg_ed25519_verify_equation}
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	pop edx
	ret
	.p2align 6
