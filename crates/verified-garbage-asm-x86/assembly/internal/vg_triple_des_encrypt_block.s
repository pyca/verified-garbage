// The functions of `src/internal/vg_triple_des_encrypt_block.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_encrypt_block:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax+128], ebp
	mov DWORD PTR [eax+132], ebx
	mov DWORD PTR [eax+136], esi
	mov DWORD PTR [eax+140], edi
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ecx]
	mov edx, DWORD PTR [ecx+4]
	bswap eax
	bswap edx
	mov esi, DWORD PTR [esp+4]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 3
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 6
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 9
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 11
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 15
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 17
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 20
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 23
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 26
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 29
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 2
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 7
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 11
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 13
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 16
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 19
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 22
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 25
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 28
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 31
	and ebx, 2097152
	xor ecx, ebx
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp]
	ror ecx, 1
	and ecx, 1024
	mov ebx, DWORD PTR [ebp]
	ror ebx, 4
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 7
	and ebx, 16777220
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 10
	and ebx, 512
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 12
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 13
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 16
	and ebx, 2
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 18
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 19
	and ebx, 256
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 21
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 24
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 25
	and ebx, 1
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp]
	ror ebx, 30
	and ebx, 33554440
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 3
	and ebx, 268435520
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 6
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 8
	and ebx, -2147483648
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 9
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 12
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 14
	and ebx, 8388608
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 15
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 17
	and ebx, 1073741824
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 20
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 21
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 23
	and ebx, 4194304
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 26
	and ebx, 536871040
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+4]
	ror ebx, 29
	and ebx, 16384
	xor ecx, ebx
	mov DWORD PTR [ebp+68], ecx
	mov eax, 3
	mov DWORD PTR [ebp+76], eax
	mov eax, 8
	mov DWORD PTR [ebp+80], eax
20:
	mov eax, 16
	mov DWORD PTR [ebp+72], eax
21:
	mov eax, DWORD PTR [ebp+68]
	ror eax, 25
	and eax, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 27
	and ecx, 258048
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 29
	and ecx, 4032
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 31
	and ecx, 63
	xor eax, ecx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 16515072
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 11
	and ecx, 258048
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 13
	and ecx, 4032
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	ror ecx, 15
	and ecx, 63
	xor ebx, ecx
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi]
	shr ecx, 24
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+4]
	and ecx, 65535
	ror ecx, 24
	xor ebx, ecx
	mov ecx, eax
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp], ecx
	mov ecx, eax
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+4], ecx
	mov ecx, eax
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+8], ecx
	mov ecx, eax
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+12], ecx
	mov ecx, eax
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+16], ecx
	mov ecx, eax
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+20], ecx
	mov ecx, ebx
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+28], ecx
	mov ecx, ebx
	shr ecx, 1
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+32], ecx
	mov ecx, ebx
	shr ecx, 2
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+36], ecx
	mov ecx, ebx
	shr ecx, 3
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+40], ecx
	mov ecx, ebx
	shr ecx, 4
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+44], ecx
	mov ecx, ebx
	shr ecx, 5
	and ecx, 266305
	mov edx, ecx
	ror edx, 31
	xor ecx, edx
	mov edx, ecx
	ror edx, 30
	xor ecx, edx
	mov DWORD PTR [ebp+48], ecx
	mov eax, DWORD PTR [ebp]
	and eax, 1598085
	xor eax, 282893
	mov ebx, DWORD PTR [ebp]
	and ebx, 3437261
	xor ebx, 1606338
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1340041
	xor ecx, 1060932
	mov ebx, DWORD PTR [ebp]
	and ebx, 3723909
	xor ebx, 2159041
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2388677
	xor edx, 3445699
	mov ebx, DWORD PTR [ebp]
	and ebx, 3699333
	xor ebx, 794639
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1372805
	xor ecx, 2908302
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461961
	xor ebx, 1315720
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 3695491
	xor edi, 524870
	mov ebx, DWORD PTR [ebp]
	and ebx, 3167173
	xor ebx, 3199372
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1601929
	xor ecx, 2400906
	mov ebx, DWORD PTR [ebp]
	and ebx, 3158729
	xor ebx, 3949383
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1864521
	xor edx, 3699465
	mov ebx, DWORD PTR [ebp]
	and ebx, 2642695
	xor ebx, 57536
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1335753
	xor ecx, 1884485
	mov ebx, DWORD PTR [ebp]
	and ebx, 3973961
	xor ebx, 2667019
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp]
	and eax, 3986249
	xor eax, 1085963
	mov ebx, DWORD PTR [ebp]
	and ebx, 840646
	xor ebx, 291086
	xor ebx, eax
	and ebx, DWORD PTR [ebp+4]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3723590
	xor ecx, 2159297
	mov ebx, DWORD PTR [ebp]
	and ebx, 1610499
	xor ebx, 2933640
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+8]
	xor eax, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 2929549
	xor edx, 795020
	mov ebx, DWORD PTR [ebp]
	and ebx, 2413379
	xor ebx, 3674693
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3187587
	xor ecx, 3429191
	mov ebx, DWORD PTR [ebp]
	and ebx, 3183247
	xor ebx, 565698
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+12]
	xor eax, edx
	mov edi, DWORD PTR [ebp]
	and edi, 2642511
	xor edi, 3989696
	mov ebx, DWORD PTR [ebp]
	and ebx, 1339590
	xor ebx, 2622403
	xor ebx, edi
	and ebx, DWORD PTR [ebp+4]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 1622346
	xor ecx, 1589574
	mov ebx, DWORD PTR [ebp]
	and ebx, 1626957
	xor ebx, 3158157
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+8]
	xor edi, ecx
	mov edx, DWORD PTR [ebp]
	and edx, 1630661
	xor edx, 1343503
	mov ebx, DWORD PTR [ebp]
	and ebx, 3461955
	xor ebx, 2413322
	xor ebx, edx
	and ebx, DWORD PTR [ebp+4]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp]
	and ecx, 3186890
	xor ecx, 45705
	mov ebx, DWORD PTR [ebp]
	and ebx, 3715530
	xor ebx, 1859652
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+4]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+8]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+12]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+16]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+24]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+20]
	xor ebx, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+56], ebx
	mov eax, DWORD PTR [ebp+28]
	and eax, 3457923
	xor eax, 3469645
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1885068
	xor ebx, 2101262
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1360460
	xor ecx, 2900555
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2642825
	xor ebx, 582085
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2380425
	xor edx, 1089920
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2904966
	xor ebx, 3961609
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3174982
	xor ecx, 1848262
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811974
	xor ebx, 295555
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 824076
	xor edi, 1593860
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2405004
	xor ebx, 1356481
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1323587
	xor ecx, 3154114
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3715654
	xor ebx, 2413452
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 2384771
	xor edx, 2671431
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2380745
	xor ebx, 786570
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1630915
	xor ecx, 37128
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3994185
	xor ebx, 3694671
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+28]
	and eax, 1888454
	xor eax, 2097859
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2924742
	xor ebx, 582025
	xor ebx, eax
	and ebx, DWORD PTR [ebp+32]
	xor eax, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 3199558
	xor ecx, 3453062
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1335881
	xor ebx, 291392
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+36]
	xor eax, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807369
	xor edx, 2908234
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3961219
	xor ebx, 3179463
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1594179
	xor ecx, 1102605
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2372492
	xor ebx, 1839118
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+40]
	xor eax, edx
	mov edi, DWORD PTR [ebp+28]
	and edi, 1369033
	xor edi, 3969871
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 3727820
	xor ebx, 2376196
	xor ebx, edi
	and ebx, DWORD PTR [ebp+32]
	xor edi, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1339593
	xor ecx, 835845
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 811980
	xor ebx, 3711179
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edi
	and ecx, DWORD PTR [ebp+36]
	xor edi, ecx
	mov edx, DWORD PTR [ebp+28]
	and edx, 807366
	xor edx, 1593996
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 1352652
	xor ebx, 1323329
	xor ebx, edx
	and ebx, DWORD PTR [ebp+32]
	xor edx, ebx
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1622211
	xor ecx, 2630082
	mov ebx, DWORD PTR [ebp+28]
	and ebx, 2925379
	xor ebx, 62344
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+32]
	xor ecx, ebx
	xor ecx, edx
	and ecx, DWORD PTR [ebp+36]
	xor edx, ecx
	xor edx, edi
	and edx, DWORD PTR [ebp+40]
	xor edi, edx
	xor edi, eax
	and edi, DWORD PTR [ebp+44]
	xor eax, edi
	mov ebx, DWORD PTR [ebp+52]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+48]
	xor ebx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+60], ebx
	mov edi, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 2
	and ecx, 270336
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 7
	and ecx, 134217729
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 11
	and ecx, 136
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 16
	and ecx, 302120960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 20
	and ecx, 1048576
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 24
	and ecx, 538970112
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 27
	and ecx, 16777248
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+56]
	ror ecx, 28
	and ecx, 1024
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 3
	and ecx, -2147483648
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 6
	and ecx, 32772
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 10
	and ecx, 4194304
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 11
	and ecx, 528
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 15
	and ecx, 1140850688
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 18
	and ecx, 2
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 23
	and ecx, 69632
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 27
	and ecx, 8912960
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+60]
	ror ecx, 30
	and ecx, 16640
	xor edi, ecx
	mov eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edi
	mov eax, DWORD PTR [ebp+80]
	add esi, eax
	mov eax, DWORD PTR [ebp+72]
	sub eax, 1
	mov DWORD PTR [ebp+72], eax
	jne 21b
	mov ecx, DWORD PTR [ebp+80]
	mov eax, 128
	sub eax, ecx
	add esi, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+64]
	mov ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+64], ecx
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+76]
	sub eax, 1
	mov DWORD PTR [ebp+76], eax
	jne 20b
	sub esi, 504
	mov ecx, DWORD PTR [ebp+64]
	and ecx, 1024
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 3
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 6
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 8
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 9
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 14
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 15
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 17
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 20
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 23
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 26
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 29
	and ebx, 1048576
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 2
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 5
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 7
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 8
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 13
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 14
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 16
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 19
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 22
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 25
	and ebx, -2147483136
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 28
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 31
	and ebx, 2048
	xor ecx, ebx
	mov DWORD PTR [ebp], ecx
	mov ecx, DWORD PTR [ebp+64]
	ror ecx, 1
	and ecx, 1048576
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 4
	and ebx, 1024
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 7
	and ebx, 4194305
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 10
	and ebx, 4096
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 12
	and ebx, 16777216
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 13
	and ebx, 4
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 16
	and ebx, 16384
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 18
	and ebx, 67108864
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 19
	and ebx, 16
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 21
	and ebx, 65536
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 24
	and ebx, 268435456
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 25
	and ebx, 64
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 27
	and ebx, 262144
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	ror ebx, 30
	and ebx, 1073742080
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, 2097152
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 3
	and ebx, 2048
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 6
	and ebx, 8388610
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 9
	and ebx, 8192
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 11
	and ebx, 33554432
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 12
	and ebx, 8
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 15
	and ebx, 32768
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 17
	and ebx, 134217728
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 18
	and ebx, 32
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 20
	and ebx, 131072
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 23
	and ebx, 536870912
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 24
	and ebx, 128
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 26
	and ebx, 524288
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+68]
	ror ebx, 29
	and ebx, -2147483136
	xor ecx, ebx
	mov DWORD PTR [ebp+4], ecx
	mov eax, DWORD PTR [ebp]
	mov edx, DWORD PTR [ebp+4]
	bswap eax
	bswap edx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+132]
	mov esi, DWORD PTR [ecx+136]
	mov edi, DWORD PTR [ecx+140]
	mov ebp, DWORD PTR [ecx+128]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	ret
	.p2align 6
