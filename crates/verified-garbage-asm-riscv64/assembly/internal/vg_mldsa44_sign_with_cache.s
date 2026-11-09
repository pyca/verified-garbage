// The functions of `src/internal/vg_mldsa44_sign_with_cache.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_with_cache:
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
	addi s11, a4, 0
	sd a3, 912(s11)
	addi s4, zero, 1
	addi t2, zero, 0
	sltu t0, t2, a6
	sub t0, t2, t0
	and s3, a5, t0
	addi a0, s10, 0
	addi a1, s11, 920
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 21f
	j 22f
21:
	addi a0, s8, 0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 32
23:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 23b
	addi a0, s9, 0
	lui a1, 1
	addi a1, a1, -2016
	add a1, s11, a1
	addi a2, zero, 64
24:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
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
	addi a3, s10, 32
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	addi a4, zero, 96
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 960
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	ld s8, 912(s11)
	bnez s3, 25f
	lui a0, 0
	addi a0, a0, 128
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 224
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 320
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 416
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 512
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 608
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 704
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 800
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 896
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1312
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1728
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -1952
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 26f
25:
	lui a0, 0
	addi a0, a0, 0
	add a0, s3, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 3
	addi a2, a2, 0
27:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 27b
26:
	addi s7, zero, 0
	addi s5, zero, 814
28:
	addi a0, s7, 0
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 1024
29:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 1
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 1024
210:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 2
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 1024
211:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 3
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
212:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 212b
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1856
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1664
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1472
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
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
	addi a4, zero, 64
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	addi a4, zero, 768
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1040
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	lui a0, 0
	addi a0, a0, 1040
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 32
	lui a2, 0
	addi a2, a2, 39
	lui a3, 1
	addi a3, a3, 1024
	add a3, s11, a3
	lui a4, 1
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_sample_in_ball}
	slli a0, a0, 32
	srli a0, a0, 32
	bnez a0, 213f
	addi s4, zero, 0
	addi s5, zero, 1
	j 214f
213:
	lui a0, 1
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi s4, zero, 1
	addi s6, zero, 0
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 215f
	j 216f
215:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 217f
	j 218f
217:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 219f
	j 220f
219:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 221f
	j 222f
221:
222:
220:
218:
216:
	bnez s4, 223f
	j 224f
223:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 225f
	j 226f
225:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 227f
	j 228f
227:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 229f
	j 230f
229:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 231f
	j 232f
231:
232:
230:
228:
226:
	bnez s4, 233f
	j 234f
233:
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
235:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 235b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
236:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
237:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 237b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, 0
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
238:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 238b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, 1024
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	addi a0, s6, -81
	srli a0, a0, 63
	and s4, s4, a0
234:
224:
	bnez s4, 239f
	addi s7, s7, 4
	j 240f
239:
	addi s5, zero, 1
240:
214:
	addi s5, s5, -1
	bnez s5, 28b
	bnez s4, 241f
	j 242f
241:
	addi a0, s11, 1040
	addi a1, s8, 0
	addi a2, zero, 32
243:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 243b
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 32
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 608
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1184
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1760
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 3
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1024
	lui a2, 0
	addi a2, a2, 80
	lui a3, 1
	addi a3, a3, -1760
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 84
	call {vg_mldsa_hint_bit_pack}
242:
22:
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
