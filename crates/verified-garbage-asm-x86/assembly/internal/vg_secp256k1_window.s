// The functions of `src/internal/vg_secp256k1_window.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_window:
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+796], eax
	mov esi, 0
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+700], eax
	mov esi, 1
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
20:
	mov eax, 1280
	mov ecx, 608
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1440
	mov ecx, 640
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1440
	mov ecx, 1280
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 608
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 1440
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 1280
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 704
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 288
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 288
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 928
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 864
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 832
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 800
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 768
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 768
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	add esi, 1
	mov eax, esi
	mov ecx, 96
	mul ecx
	mov edx, edi
	add edx, 4876
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm1, XMMWORD PTR [edi+720]
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm2, XMMWORD PTR [edi+736]
	movdqu XMMWORD PTR [edx+32], xmm2
	movdqu xmm3, XMMWORD PTR [edi+752]
	movdqu XMMWORD PTR [edx+48], xmm3
	movdqu xmm4, XMMWORD PTR [edi+768]
	movdqu XMMWORD PTR [edx+64], xmm4
	movdqu xmm5, XMMWORD PTR [edi+784]
	movdqu XMMWORD PTR [edx+80], xmm5
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+700], eax
	cmp esi, 15
	jne 20b
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+604], eax
	mov esi, 64
21:
	sub esi, 1
	mov eax, 576
	mov ecx, 512
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 576
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 544
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 576
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 608
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 608
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 640
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 768
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 928
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 896
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 928
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 736
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 704
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 928
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 896
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 608
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 640
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 608
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 640
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 768
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 928
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 896
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 928
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 704
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 736
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 832
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 704
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 928
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 896
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 864
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 512
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 672
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 800
	mov edx, 576
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 640
	mov edx, 544
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+576]
	or edx, DWORD PTR [edi+580]
	or edx, DWORD PTR [edi+584]
	or edx, DWORD PTR [edi+588]
	or edx, DWORD PTR [edi+592]
	or edx, DWORD PTR [edi+596]
	or edx, DWORD PTR [edi+600]
	or edx, DWORD PTR [edi+604]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov ecx, edx
	mov eax, DWORD PTR [edi+224]
	mov edx, DWORD PTR [edi+544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+228]
	mov edx, DWORD PTR [edi+548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+232]
	mov edx, DWORD PTR [edi+552]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+236]
	mov edx, DWORD PTR [edi+556]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+240]
	mov edx, DWORD PTR [edi+560]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+244]
	mov edx, DWORD PTR [edi+564]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+248]
	mov edx, DWORD PTR [edi+568]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+252]
	mov edx, DWORD PTR [edi+572]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	cmp esi, 63
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
	add edx, 4876
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
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 5
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
	mov ecx, 6
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
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
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
	mov ecx, 10
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
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 11
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
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
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
	mov ecx, 14
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
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm1
	movdqu XMMWORD PTR [edi+736], xmm2
	movdqu XMMWORD PTR [edi+752], xmm3
	movdqu XMMWORD PTR [edi+768], xmm4
	movdqu XMMWORD PTR [edi+784], xmm5
	mov eax, 704
	mov ecx, 512
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 544
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 576
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 512
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 704
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 800
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 896
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 544
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 736
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 512
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 704
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 608
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 608
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 288
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 288
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 928
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 864
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 832
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 896
	mov ecx, 800
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 672
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_secp256k1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+572], eax
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
	test esi, esi
	jne 21b
	ret
	.p2align 6
