// The functions of `src/sha512.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init:
	.option push
	.option arch, +m, +c
	lui t0, 834490
	addiw t0, t0, -674
	slli t0, t0, 32
	lui t1, 790618
	addiw t1, t1, -296
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 403875
	addiw t0, t0, -1750
	slli t0, t0, 32
	lui t1, 223181
	addiw t1, t1, 1287
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 595344
	addiw t0, t0, 346
	slli t0, t0, 32
	lui t1, 198414
	addiw t1, t1, -745
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 86783
	addiw t0, t0, -807
	slli t0, t0, 32
	lui t1, 1011942
	addiw t1, t1, -1735
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 422706
	addiw t0, t0, 1640
	slli t0, t0, 32
	lui t1, 1047553
	addiw t1, t1, -1231
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 584517
	addiw t0, t0, -1401
	slli t0, t0, 32
	lui t1, 427393
	addiw t1, t1, 1297
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 897219
	addiw t0, t0, -499
	slli t0, t0, 32
	lui t1, 413593
	addiw t1, t1, -89
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 293717
	addiw t0, t0, -2018
	slli t0, t0, 32
	lui t1, 782245
	addiw t1, t1, -92
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_init:
	.option push
	.option arch, +m, +c
	lui t0, 434334
	addiw t0, t0, 1640
	slli t0, t0, 32
	lui t1, 998349
	addiw t1, t1, -1784
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 767611
	addiw t0, t0, -378
	slli t0, t0, 32
	lui t1, 543914
	addiw t1, t1, 1851
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 247535
	addiw t0, t0, 883
	slli t0, t0, 32
	lui t1, 1042768
	addiw t1, t1, -2005
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	slli t0, t0, 32
	lui t1, 389587
	addiw t1, t1, 1777
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 332005
	addiw t0, t0, 640
	slli t0, t0, 32
	lui t1, 712296
	addiw t1, t1, 721
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	slli t0, t0, 32
	lui t1, 177127
	addiw t1, t1, -993
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 129086
	addiw t0, t0, -1620
	slli t0, t0, 32
	lui t1, 1029148
	addiw t1, t1, -661
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 376333
	addiw t0, t0, -743
	slli t0, t0, 32
	lui t1, 79842
	addiw t1, t1, 377
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_224_init:
	.option push
	.option arch, +m, +c
	lui t0, 574419
	addiw t0, t0, 1992
	slli t0, t0, 32
	lui t1, 103749
	addiw t1, t1, -606
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 474650
	addiw t0, t0, -1689
	slli t0, t0, 32
	lui t1, 564685
	addiw t1, t1, 1238
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 122795
	addiw t0, t0, 1966
	slli t0, t0, 32
	lui t1, 208890
	addiw t1, t1, -894
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 424413
	addiw t0, t0, 1300
	slli t0, t0, 32
	lui t1, 361210
	addiw t1, t1, -49
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 63187
	addiw t0, t0, -1175
	slli t0, t0, 32
	lui t1, 507205
	addiw t1, t1, -600
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 491063
	addiw t0, t0, -141
	slli t0, t0, 32
	lui t1, 19529
	addiw t1, t1, -1726
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 260568
	addiw t0, t0, 1448
	slli t0, t0, 32
	lui t1, 434643
	addiw t1, t1, 1736
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 69934
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 597353
	addiw t1, t1, 673
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_256_init:
	.option push
	.option arch, +m, +c
	lui t0, 140050
	addiw t0, t0, 405
	slli t0, t0, 32
	lui t1, 1032895
	addiw t1, t1, 1836
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 652630
	addiw t0, t0, -92
	slli t0, t0, 32
	lui t1, 820422
	addiw t1, t1, 1218
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 145724
	addiw t0, t0, -1941
	slli t0, t0, 32
	lui t1, 455995
	addiw t1, t1, 337
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 615303
	addiw t0, t0, 1817
	slli t0, t0, 32
	lui t1, 365583
	addiw t1, t1, -1347
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 615044
	addiw t0, t0, -285
	slli t0, t0, 32
	lui t1, 690416
	addiw t1, t1, -29
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 779746
	addiw t0, t0, -475
	slli t0, t0, 32
	lui t1, 342116
	addiw t1, t1, -1646
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 176154
	addiw t0, t0, -1540
	slli t0, t0, 32
	lui t1, 182364
	addiw t1, t1, -1878
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 60275
	addiw t0, t0, -547
	slli t0, t0, 32
	lui t1, 531539
	addiw t1, t1, -862
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 127
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -128
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 7
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 128
	addi s4, s4, -128
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -128
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	lbu t1, 48(s1)
	lbu t2, 49(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 52(s1)
	lbu t2, 53(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 54(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 55(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 48(s3)
	srli t2, t1, 48
	sb t2, 49(s3)
	srli t2, t1, 40
	sb t2, 50(s3)
	srli t2, t1, 32
	sb t2, 51(s3)
	srli t2, t1, 24
	sb t2, 52(s3)
	srli t2, t1, 16
	sb t2, 53(s3)
	srli t2, t1, 8
	sb t2, 54(s3)
	srli t2, t1, 0
	sb t2, 55(s3)
	lbu t1, 56(s1)
	lbu t2, 57(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 58(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 59(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 60(s1)
	lbu t2, 61(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 62(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 63(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 56(s3)
	srli t2, t1, 48
	sb t2, 57(s3)
	srli t2, t1, 40
	sb t2, 58(s3)
	srli t2, t1, 32
	sb t2, 59(s3)
	srli t2, t1, 24
	sb t2, 60(s3)
	srli t2, t1, 16
	sb t2, 61(s3)
	srli t2, t1, 8
	sb t2, 62(s3)
	srli t2, t1, 0
	sb t2, 63(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha384_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_256_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_224_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop
