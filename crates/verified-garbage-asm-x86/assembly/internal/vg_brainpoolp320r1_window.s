// The functions of `src/internal/vg_brainpoolp320r1_window.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_window:
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+980], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 128
	mul ecx
	mov edx, edi
	add edx, 5068
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+864]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+880]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+896]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+912]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+928]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+944]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+960]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+976]
	movdqu XMMWORD PTR [edx+112], xmm0
	mov eax, DWORD PTR [edi+1584]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1588]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1592]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1596]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+1792]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+1796]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+1800]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+1804]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+1808]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+1812]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1584]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1588]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1592]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1596]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1600]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1604]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1608]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1612]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1616]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1620]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+1784]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1788]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1792]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1796]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1800]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1804]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1808]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1812]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+860], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 128
	mul ecx
	mov edx, edi
	add edx, 5068
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+864]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+880]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+896]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+912]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+928]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+944]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+960]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+976]
	movdqu XMMWORD PTR [edx+112], xmm0
20:
	mov eax, 1584
	mov ecx, 744
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1784
	mov ecx, 784
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 264
	mov ecx, 824
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 744
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1784
	mov ecx, 1584
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 984
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 264
	mov ecx, 1584
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 784
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 264
	mov ecx, 1784
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 344
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 864
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 1024
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 1024
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 864
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 344
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1024
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 904
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1184
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1104
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1104
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 1184
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 944
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 128
	mul ecx
	mov edx, edi
	add edx, 5068
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+864]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+880]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+896]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+912]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+928]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+944]
	movdqu XMMWORD PTR [edx+80], xmm5
	movdqu xmm0, XMMWORD PTR [edi+960]
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+976]
	movdqu XMMWORD PTR [edx+112], xmm0
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+944]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+948]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+952]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+956]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+860], eax
	cmp esi, 15
	jne 20b
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+740], eax
	mov esi, 80
21:
	sub esi, 1
	mov eax, 704
	mov ecx, 624
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 664
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 704
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 744
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 784
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 744
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 824
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 784
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 944
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1104
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 1144
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 904
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 904
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 864
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 944
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 904
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 824
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1104
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 1144
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 784
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 744
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 784
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 744
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 824
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 784
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 944
	mov edx, 944
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 1104
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 1144
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 904
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 904
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 864
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 944
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 904
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 824
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1144
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1104
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1104
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 1144
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1064
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 784
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 824
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 984
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 184
	mov ecx, 784
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+704]
	or edx, DWORD PTR [edi+708]
	or edx, DWORD PTR [edi+712]
	or edx, DWORD PTR [edi+716]
	or edx, DWORD PTR [edi+720]
	or edx, DWORD PTR [edi+724]
	or edx, DWORD PTR [edi+728]
	or edx, DWORD PTR [edi+732]
	or edx, DWORD PTR [edi+736]
	or edx, DWORD PTR [edi+740]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov ecx, edx
	mov eax, DWORD PTR [edi+264]
	mov edx, DWORD PTR [edi+664]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+268]
	mov edx, DWORD PTR [edi+668]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+272]
	mov edx, DWORD PTR [edi+672]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+676]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+280]
	mov edx, DWORD PTR [edi+680]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+284]
	mov edx, DWORD PTR [edi+684]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+288]
	mov edx, DWORD PTR [edi+688]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+292]
	mov edx, DWORD PTR [edi+692]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+296]
	mov edx, DWORD PTR [edi+696]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+300]
	mov edx, DWORD PTR [edi+700]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+700], eax
	cmp esi, 79
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
	add edx, 5068
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
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
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1968]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+864], xmm0
	movdqu XMMWORD PTR [edi+880], xmm1
	movdqu XMMWORD PTR [edi+896], xmm2
	movdqu XMMWORD PTR [edi+912], xmm3
	movdqu XMMWORD PTR [edi+928], xmm4
	movdqu XMMWORD PTR [edi+944], xmm5
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 4
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
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 9
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
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm1, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu XMMWORD PTR [edi+960], xmm0
	movdqu XMMWORD PTR [edi+976], xmm1
	mov eax, 864
	mov ecx, 624
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 664
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 704
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 624
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 904
	mov ecx, 864
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 984
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1104
	mov edx, 1104
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 624
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 864
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1184
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 664
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 944
	mov ecx, 904
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1184
	mov edx, 1184
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 304
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 344
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1024
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1024
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 744
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 984
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 344
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 984
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 304
	mov edx, 1064
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1064
	mov ecx, 1144
	mov edx, 1144
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1024
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 784
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1184
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 744
	mov ecx, 1104
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 744
	mov edx, 744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1104
	mov edx, 984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 824
	mov ecx, 1184
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 984
	mov ecx, 824
	mov edx, 824
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp320r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+740], eax
	test esi, esi
	jne 21b
	ret
	.p2align 6
