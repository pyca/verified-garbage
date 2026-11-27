// The functions of `src/internal/vg_p192_window.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_window:
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+612], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 80
	mul ecx
	mov edx, edi
	add edx, 4684
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+576]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+592]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+608]
	movdqu XMMWORD PTR [edx+64], xmm4
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+540], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 80
	mul ecx
	mov edx, edi
	add edx, 4684
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+576]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+592]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+608]
	movdqu XMMWORD PTR [edx+64], xmm4
20:
	mov eax, 976
	mov ecx, 472
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1096
	mov ecx, 496
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 520
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 496
	mov ecx, 472
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1096
	mov ecx, 976
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 616
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 976
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 496
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 1096
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 208
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 232
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 544
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 640
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 640
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 544
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 616
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 232
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 640
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 568
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 736
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 688
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 544
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 688
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 736
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 592
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 80
	mul ecx
	mov edx, edi
	add edx, 4684
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+576]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+592]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+608]
	movdqu XMMWORD PTR [edx+64], xmm4
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+540], eax
	cmp esi, 15
	jne 20b
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+468], eax
	mov esi, 48
21:
	sub esi, 1
	mov eax, 448
	mov ecx, 400
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 448
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 424
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 136
	mov ecx, 448
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 520
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 496
	mov ecx, 496
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 472
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 544
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 664
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 496
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 592
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 544
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 544
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 664
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 688
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 568
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 592
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 568
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 544
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 544
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 544
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 472
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 664
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 568
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 520
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 664
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 496
	mov ecx, 688
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 496
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 520
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 496
	mov ecx, 496
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 472
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 544
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 664
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 496
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 592
	mov edx, 592
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 544
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 544
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 664
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 688
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 568
	mov edx, 568
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 592
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 568
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 544
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 544
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 544
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 472
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 664
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 568
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 520
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 688
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 664
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 496
	mov ecx, 688
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 496
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 400
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 520
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 616
	mov edx, 448
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 136
	mov ecx, 496
	mov edx, 424
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+448]
	or edx, DWORD PTR [edi+452]
	or edx, DWORD PTR [edi+456]
	or edx, DWORD PTR [edi+460]
	or edx, DWORD PTR [edi+464]
	or edx, DWORD PTR [edi+468]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov ecx, edx
	mov eax, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+204]
	mov edx, DWORD PTR [edi+444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+444], eax
	cmp esi, 47
	je 22f
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	jmp 23f
22:
	mov eax, esi
	mov ecx, 4
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
23:
	mov ebx, eax
	add ebx, 1
	mov edx, edi
	add edx, 4684
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm4, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu XMMWORD PTR [edi+592], xmm3
	movdqu XMMWORD PTR [edi+608], xmm4
	mov eax, 544
	mov ecx, 400
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 424
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 448
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 400
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 544
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 616
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 400
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 544
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 424
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 568
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 208
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 232
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 616
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 232
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 640
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 496
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 736
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 688
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 736
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 520
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+468], eax
	test esi, esi
	jne 21b
	ret
	.p2align 6
