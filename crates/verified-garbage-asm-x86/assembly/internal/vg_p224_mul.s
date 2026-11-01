// The functions of `src/internal/vg_p224_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, 32
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1056]
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
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+544]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+548]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+552]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+556]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+560]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+564]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+568]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+572]
	mov DWORD PTR [edi+1052], eax
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
	mov esi, 256
21:
	sub esi, 1
	mov eax, 512
	mov ecx, 512
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 544
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 576
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 544
	mov ecx, 512
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
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
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
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
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 512
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 512
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 544
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 544
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 256
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 288
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 832
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 288
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 832
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 960
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 608
	mov ecx, 896
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 608
	mov edx, 608
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 960
	mov edx, 672
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 992
	mov ecx, 608
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 640
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 224
	mov ecx, 672
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 608
	mov edx, 896
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 992
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
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
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
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
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 608
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 224
	mov ecx, 992
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 960
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 672
	mov ecx, 640
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 224
	mov ecx, 1024
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 832
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 960
	mov edx, 960
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 256
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 288
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 704
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 832
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 832
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 704
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 800
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 832
	mov edx, 832
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 288
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 800
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 256
	mov edx, 864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 864
	mov ecx, 928
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 832
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 928
	mov ecx, 960
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 896
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 800
	mov ecx, 704
	mov edx, 704
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 832
	mov ecx, 896
	mov edx, 800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 768
	mov ecx, 960
	mov edx, 768
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
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
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+608]
	mov edx, DWORD PTR [edi+704]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+612]
	mov edx, DWORD PTR [edi+708]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+516], eax
	mov eax, DWORD PTR [edi+616]
	mov edx, DWORD PTR [edi+712]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [edi+620]
	mov edx, DWORD PTR [edi+716]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [edi+624]
	mov edx, DWORD PTR [edi+720]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+628]
	mov edx, DWORD PTR [edi+724]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+632]
	mov edx, DWORD PTR [edi+728]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+636]
	mov edx, DWORD PTR [edi+732]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+736]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+740]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+744]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+748]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+752]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+756]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+760]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+764]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+604], eax
	test esi, esi
	jne 21b
	mov edx, edi
	mov ebx, DWORD PTR [edx+1504]
	mov esi, DWORD PTR [edx+1508]
	mov ebp, DWORD PTR [edx+1516]
	mov edi, DWORD PTR [edx+1512]
	ret
	.p2align 6
