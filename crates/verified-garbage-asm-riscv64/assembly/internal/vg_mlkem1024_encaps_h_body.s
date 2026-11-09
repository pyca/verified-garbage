// The functions of `src/internal/vg_mlkem1024_encaps_h_body.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_encaps_h_body:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a5)
	sd s4, 1296(a5)
	sd s5, 1304(a5)
	sd s6, 1312(a5)
	sd s7, 1320(a5)
	sd s8, 1328(a5)
	sd s9, 1336(a5)
	sd s10, 1344(a5)
	sd s11, 1352(a5)
	sd ra, 1360(a5)
	addi s10, a0, 0
	addi s9, a2, 0
	addi s8, a3, 0
	addi s7, a4, 0
	addi s11, a5, 0
	addi a0, a1, 0
	addi a1, s11, 992
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi a0, s9, 0
	addi a1, s11, 1024
	addi a2, zero, 32
21:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
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
22:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 22b
	addi a0, s10, 1536
	addi a1, s11, 1248
	addi a2, zero, 32
23:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 23b
	addi s6, zero, 0
24:
	addi t0, zero, 384
	mul t0, s6, t0
	add a0, s10, t0
	addi a1, s6, 2
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_decode12}
	addi s6, s6, 1
	addi t0, s6, -4
	bnez t0, 24b
	addi s6, zero, 0
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
	addi a1, s6, 6
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi a0, s6, 6
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 21
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_ntt}
	addi s6, s6, 1
	addi t0, s6, -4
	bnez t0, 25b
	addi s6, zero, 4
26:
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
	addi a1, s6, 6
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_cbd2}
	addi s6, s6, 1
	addi t0, s6, -9
	bnez t0, 26b
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, zero, 1
	addi a3, zero, 15
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_decode_decompress}
	addi s4, zero, 1
	addi s6, zero, 0
27:
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
28:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 28b
	addi s5, zero, 0
29:
	sb s6, 1280(s11)
	sb s5, 1281(s11)
	addi a0, s11, 1248
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, zero, 19
	slli a2, a2, 10
	add a2, s11, a2
	call {vg_mlkem_sample_ntt}
	and s4, s4, a0
	beqz a0, 210f
	addi a1, zero, 18
	slli a1, a1, 10
	add a1, s11, a1
	j 211f
210:
	addi a1, s5, 6
	slli a1, a1, 10
	add a1, s11, a1
211:
	addi a0, zero, 17
	slli a0, a0, 10
	add a0, s11, a0
	addi a2, s5, 6
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 21
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 17
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -4
	bnez t0, 29b
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 21
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s6, 10
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi t0, zero, 352
	mul t0, s6, t0
	add a2, s7, t0
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 11
	addi a3, zero, 352
	call {vg_mlkem1024_compress_encode}
	addi s6, s6, 1
	addi t0, s6, -4
	bnez t0, 27b
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 0
	addi a2, zero, 256
212:
	sw a1, 0(a0)
	addi a0, a0, 4
	addi a2, a2, -1
	bnez a2, 212b
	addi s5, zero, 0
213:
	addi a0, zero, 17
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, s5, 2
	slli a1, a1, 10
	add a1, s11, a1
	addi a2, s5, 6
	slli a2, a2, 10
	add a2, s11, a2
	addi a3, zero, 21
	slli a3, a3, 10
	add a3, s11, a3
	call {vg_mlkem_multiply_ntts}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 17
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi s5, s5, 1
	addi t0, s5, -4
	bnez t0, 213b
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 21
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_inv_ntt}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 14
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 15
	slli a1, a1, 10
	add a1, s11, a1
	call {vg_mlkem_add}
	addi a0, zero, 16
	slli a0, a0, 10
	add a0, s11, a0
	addi a1, zero, 5
	addi a2, s7, 1408
	addi a3, zero, 160
	call {vg_mlkem1024_compress_encode}
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
