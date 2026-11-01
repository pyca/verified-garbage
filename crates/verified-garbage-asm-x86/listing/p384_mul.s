// The functions of `src/p384_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+2224], ebx
	mov DWORD PTR [eax+2228], esi
	mov DWORD PTR [eax+2232], edi
	mov DWORD PTR [eax+2236], ebp
	mov edi, eax
	mov esi, 48
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1552]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+1500], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+1504], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+1508], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+1512], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+1516], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+876], eax
	mov esi, 384
21:
	sub esi, 1
	mov eax, 736
	mov ecx, 736
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 784
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 736
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 736
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1168
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 736
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 736
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 784
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 784
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 352
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 400
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1216
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1168
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 400
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1216
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1408
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 880
	mov ecx, 1312
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 880
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1312
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 1408
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 976
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1456
	mov ecx, 880
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 928
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 976
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 880
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1504
	mov ecx, 1456
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1168
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1312
	mov edx, 1312
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 880
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 1456
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1408
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 976
	mov ecx, 928
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 1504
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 352
	mov edx, 1120
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 400
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1024
	mov edx, 1120
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1216
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1216
	mov edx, 1120
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1024
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1168
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 400
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1168
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 352
	mov edx, 1264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1264
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1216
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1072
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1360
	mov ecx, 1408
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1312
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1024
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1312
	mov edx, 1168
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1120
	mov ecx, 1408
	mov edx, 1120
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1168
	mov ecx, 1120
	mov edx, 1120
	push eax
	push ecx
	push edx
	push edi
	call {vg_p384_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+880]
	mov edx, DWORD PTR [edi+1024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+884]
	mov edx, DWORD PTR [edi+1028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+888]
	mov edx, DWORD PTR [edi+1032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+892]
	mov edx, DWORD PTR [edi+1036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+896]
	mov edx, DWORD PTR [edi+1040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+900]
	mov edx, DWORD PTR [edi+1044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+904]
	mov edx, DWORD PTR [edi+1048]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+908]
	mov edx, DWORD PTR [edi+1052]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+912]
	mov edx, DWORD PTR [edi+1056]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+916]
	mov edx, DWORD PTR [edi+1060]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+920]
	mov edx, DWORD PTR [edi+1064]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+924]
	mov edx, DWORD PTR [edi+1068]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+928]
	mov edx, DWORD PTR [edi+1072]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+932]
	mov edx, DWORD PTR [edi+1076]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+936]
	mov edx, DWORD PTR [edi+1080]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+940]
	mov edx, DWORD PTR [edi+1084]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+944]
	mov edx, DWORD PTR [edi+1088]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+948]
	mov edx, DWORD PTR [edi+1092]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+952]
	mov edx, DWORD PTR [edi+1096]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+956]
	mov edx, DWORD PTR [edi+1100]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+960]
	mov edx, DWORD PTR [edi+1104]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+964]
	mov edx, DWORD PTR [edi+1108]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+968]
	mov edx, DWORD PTR [edi+1112]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+972]
	mov edx, DWORD PTR [edi+1116]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+976]
	mov edx, DWORD PTR [edi+1120]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+980]
	mov edx, DWORD PTR [edi+1124]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+984]
	mov edx, DWORD PTR [edi+1128]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+988]
	mov edx, DWORD PTR [edi+1132]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+992]
	mov edx, DWORD PTR [edi+1136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+996]
	mov edx, DWORD PTR [edi+1140]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1000]
	mov edx, DWORD PTR [edi+1144]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1004]
	mov edx, DWORD PTR [edi+1148]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+1008]
	mov edx, DWORD PTR [edi+1152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1012]
	mov edx, DWORD PTR [edi+1156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1016]
	mov edx, DWORD PTR [edi+1160]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1020]
	mov edx, DWORD PTR [edi+1164]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+876], eax
	test esi, esi
	jne 21b
	mov edx, edi
	mov ebx, DWORD PTR [edx+2224]
	mov esi, DWORD PTR [edx+2228]
	mov ebp, DWORD PTR [edx+2236]
	mov edi, DWORD PTR [edx+2232]
	ret
	.p2align 6
