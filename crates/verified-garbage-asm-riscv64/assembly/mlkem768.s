// The functions of `src/mlkem768.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a3)
	sd s4, 1296(a3)
	sd s5, 1304(a3)
	sd s6, 1312(a3)
	sd s7, 1320(a3)
	sd s8, 1328(a3)
	sd s9, 1336(a3)
	sd s10, 1344(a3)
	sd s11, 1352(a3)
	sd ra, 1360(a3)
	addi s10, a0, 0
	addi s9, a1, 0
	addi s8, a2, 0
	addi s11, a3, 0
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s10, 0
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 1184
	addi a4, zero, 1
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 920
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	addi a0, s11, 920
	addi a1, s11, 1248
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi s6, zero, 0
21:
	sb s6, 984(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 952
	addi a4, zero, 33
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1056
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1056
	addi a1, s6, 5
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi a0, s6, 5
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_ntt}
	addi s6, s6, 1
	addi t0, s6, -6
	bnez t0, 21b
	addi s4, zero, 1
	addi s6, zero, 0
22:
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
23:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 23b
	addi s5, zero, 0
24:
	sb s5, 1280(s11)
	sb s6, 1281(s11)
	addi a0, s11, 1248
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, zero, 16
	slli a2, a2, 10
	add a2, s11, a2
	call {vg_mlkem_sample_ntt}
	and s4, s4, a0
	beqz a0, 25f
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	j 26f
25:
	addi a1, s5, 5
	slli a1, a1, 10
	add a1, s11, a1
26:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 24b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s6, 8
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi t0, zero, 384
	mul t0, s6, t0
	add a1, s9, t0
	call {vg_mlkem_encode12}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 22b
	addi s6, zero, 0
27:
	addi a0, s6, 5
	slli a0, a0, 10
	add a0, s11, a0
	addi t0, zero, 384
	mul t0, s6, t0
	add a1, s8, t0
	call {vg_mlkem_encode12}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 27b
	addi a0, s11, 1248
	addi a1, s9, 1152
	addi a2, zero, 32
28:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	addi a0, s9, 0
	addi a1, s8, 1152
	addi a2, zero, 1184
29:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s9, 0
	addi a4, zero, 1184
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -1760
	add a3, s8, a3
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	addi a0, s10, 32
	lui a1, 1
	addi a1, a1, -1728
	add a1, s8, a1
	addi a2, zero, 32
210:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi a0, s4, 0
	ld ra, 1360(s11)
	ld s3, 1288(s11)
	ld s4, 1296(s11)
	ld s5, 1304(s11)
	ld s6, 1312(s11)
	ld s7, 1320(s11)
	ld s8, 1328(s11)
	ld s9, 1336(s11)
	ld s10, 1344(s11)
	ld s11, 1352(s11)
	ret
	.option pop

vg_mlkem768_encaps:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a4)
	sd s4, 1296(a4)
	sd s5, 1304(a4)
	sd s6, 1312(a4)
	sd s7, 1320(a4)
	sd s8, 1328(a4)
	sd s9, 1336(a4)
	sd s10, 1344(a4)
	sd s11, 1352(a4)
	sd ra, 1360(a4)
	addi s10, a0, 0
	addi s9, a1, 0
	addi s8, a2, 0
	addi s7, a3, 0
	addi s11, a4, 0
	addi a0, s9, 0
	addi a1, s11, 1024
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi s9, s11, 1024
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s10, 0
	addi a4, zero, 1184
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 992
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 1024
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 992
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 920
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	addi a0, s11, 920
	addi a1, s8, 0
	addi a2, zero, 32
21:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
	addi a0, s10, 1152
	addi a1, s11, 1248
	addi a2, zero, 32
22:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 22b
	addi s6, zero, 0
23:
	addi t0, zero, 384
	mul t0, s6, t0
	add a0, s10, t0
	addi a1, s6, 2
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_decode12}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 23b
	addi s6, zero, 0
24:
	sb s6, 984(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 952
	addi a4, zero, 33
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1056
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1056
	addi a1, s6, 5
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi a0, s6, 5
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_ntt}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 24b
	addi s6, zero, 3
25:
	sb s6, 984(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 952
	addi a4, zero, 33
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1056
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1056
	addi a1, s6, 5
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi s6, s6, 1
	addi t0, s6, -7
	bnez t0, 25b
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, zero, 1
	addi a3, zero, 12
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_decode_decompress}
	addi s4, zero, 1
	addi s6, zero, 0
26:
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
27:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 27b
	addi s5, zero, 0
28:
	sb s6, 1280(s11)
	sb s5, 1281(s11)
	addi a0, s11, 1248
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, zero, 16
	slli a2, a2, 10
	add a2, s11, a2
	call {vg_mlkem_sample_ntt}
	and s4, s4, a0
	beqz a0, 29f
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	j 210f
29:
	addi a1, s5, 5
	slli a1, a1, 10
	add a1, s11, a1
210:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 28b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s6, 8
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi t0, zero, 320
	mul t0, s6, t0
	add a2, s7, t0
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 10
	addi a3, zero, 320
	call {vg_mlkem_compress_encode}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 26b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
211:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 211b
	addi s5, zero, 0
212:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s5, 2
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 212b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 11
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 12
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 4
	addi a2, s7, 960
	addi a3, zero, 128
	call {vg_mlkem_compress_encode}
	addi a0, s4, 0
	ld ra, 1360(s11)
	ld s3, 1288(s11)
	ld s4, 1296(s11)
	ld s5, 1304(s11)
	ld s6, 1312(s11)
	ld s7, 1320(s11)
	ld s8, 1328(s11)
	ld s9, 1336(s11)
	ld s10, 1344(s11)
	ld s11, 1352(s11)
	ret
	.option pop

vg_mlkem768_decaps:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a3)
	sd s4, 1296(a3)
	sd s5, 1304(a3)
	sd s6, 1312(a3)
	sd s7, 1320(a3)
	sd s8, 1328(a3)
	sd s9, 1336(a3)
	sd s10, 1344(a3)
	sd s11, 1352(a3)
	sd ra, 1360(a3)
	addi s3, a2, 0
	addi s10, a0, 0
	addi s8, a1, 0
	addi s11, a3, 0
	addi a0, s8, 0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 1088
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	lui s8, 6
	addi s8, s8, 0
	add s8, s11, s8
	addi s6, zero, 0
21:
	addi t0, zero, 320
	mul t0, s6, t0
	add a0, s8, t0
	addi a1, zero, 320
	addi a2, zero, 10
	addi a3, s6, 5
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_decode_decompress}
	addi a0, s6, 5
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_ntt}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 21b
	addi s6, zero, 0
22:
	addi t0, zero, 384
	mul t0, s6, t0
	add a0, s10, t0
	addi a1, s6, 2
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_decode12}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 22b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
23:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 23b
	addi s5, zero, 0
24:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s5, 2
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 24b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, s8, 960
	addi a1, zero, 128
	addi a2, zero, 4
	addi a3, zero, 11
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_decode_decompress}
	addi a0, zero, 11
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 13
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_sub}
	addi a0, zero, 11
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 1
	addi a2, s11, 1024
	addi a3, zero, 32
	call {vg_mlkem_compress_encode}
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 1024
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	lui a3, 1
	addi a3, a3, -1760
	add a3, s10, a3
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 72
	addi a3, s11, 920
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -1728
	add a3, s10, a3
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 6
	addi a3, a3, 0
	add a3, s11, a3
	addi a4, zero, 1088
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1216
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	addi s10, s10, 1152
	addi s9, s11, 1024
	addi s7, zero, 19
	slli s7, s7, 10
	add s7, s11, s7
	addi a0, s10, 1152
	addi a1, s11, 1248
	addi a2, zero, 32
25:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 25b
	addi s6, zero, 0
26:
	addi t0, zero, 384
	mul t0, s6, t0
	add a0, s10, t0
	addi a1, s6, 2
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_decode12}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 26b
	addi s6, zero, 0
27:
	sb s6, 984(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 952
	addi a4, zero, 33
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1056
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1056
	addi a1, s6, 5
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi a0, s6, 5
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_ntt}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 27b
	addi s6, zero, 3
28:
	sb s6, 984(s11)
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 952
	addi a4, zero, 33
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1056
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1056
	addi a1, s6, 5
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi s6, s6, 1
	addi t0, s6, -7
	bnez t0, 28b
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, zero, 1
	addi a3, zero, 12
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_decode_decompress}
	addi s4, zero, 1
	addi s6, zero, 0
29:
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
210:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 210b
	addi s5, zero, 0
211:
	sb s6, 1280(s11)
	sb s5, 1281(s11)
	addi a0, s11, 1248
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, zero, 16
	slli a2, a2, 10
	add a2, s11, a2
	call {vg_mlkem_sample_ntt}
	and s4, s4, a0
	beqz a0, 212f
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	j 213f
212:
	addi a1, s5, 5
	slli a1, a1, 10
	add a1, s11, a1
213:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 211b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s6, 8
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi t0, zero, 320
	mul t0, s6, t0
	add a2, s7, t0
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 10
	addi a3, zero, 320
	call {vg_mlkem_compress_encode}
	addi s6, s6, 1
	addi t0, s6, -3
	bnez t0, 29b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
214:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 214b
	addi s5, zero, 0
215:
	addi a0, zero, 14
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s5, 2
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, s5, 5
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 18
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -3
	bnez t0, 215b
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 11
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 12
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 13
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 4
	addi a2, s7, 960
	addi a3, zero, 128
	call {vg_mlkem_compress_encode}
	addi a0, s8, 0
	addi a1, s7, 0
	addi t2, zero, 0
	addi s6, zero, 1088
216:
	lbu a2, 0(a0)
	lbu a3, 0(a1)
	xor a2, a2, a3
	or t2, t2, a2
	addi a0, a0, 1
	addi a1, a1, 1
	addi s6, s6, -1
	bnez s6, 216b
	addi t2, t2, -1
	srli t2, t2, 63
	addi a0, zero, 0
	sub t2, a0, t2
	addi a0, s11, 920
	addi a1, s11, 1216
	addi a2, s3, 0
	addi s6, zero, 32
217:
	lbu a3, 0(a0)
	lbu a4, 0(a1)
	xor a3, a3, a4
	and a3, a3, t2
	xor a3, a3, a4
	sb a3, 0(a2)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, 1
	addi s6, s6, -1
	bnez s6, 217b
	addi a0, s4, 0
	ld ra, 1360(s11)
	ld s3, 1288(s11)
	ld s4, 1296(s11)
	ld s5, 1304(s11)
	ld s6, 1312(s11)
	ld s7, 1320(s11)
	ld s8, 1328(s11)
	ld s9, 1336(s11)
	ld s10, 1344(s11)
	ld s11, 1352(s11)
	ret
	.option pop

vg_mlkem768_check_ek:
	.option push
	.option arch, +m, +c
	addi a1, zero, 384
	addi a2, zero, 0
	lui a5, 1
	addi a5, a5, -768
20:
	lbu a3, 1(a0)
	slli a3, a3, 60
	srli a3, a3, 52
	lbu a4, 0(a0)
	add a3, a3, a4
	sub a4, a5, a3
	srli a4, a4, 63
	add a2, a2, a4
	lbu a3, 1(a0)
	srli a3, a3, 4
	lbu a4, 2(a0)
	slli a4, a4, 4
	add a3, a3, a4
	sub a4, a5, a3
	srli a4, a4, 63
	add a2, a2, a4
	addi a0, a0, 3
	addi a1, a1, -1
	bnez a1, 20b
	addi a3, zero, 0
	sub a3, a3, a2
	srli a3, a3, 63
	addi a0, zero, 1
	sub a0, a0, a3
	ret
	.option pop
