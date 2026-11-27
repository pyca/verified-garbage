// The functions of `src/internal/vg_sm4_expand_key_shared.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key_shared:
	.option push
	.option arch, +m, +c
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 320(a5)
	lui t0, 1044496
	addiw t0, t0, -255
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 328(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 336(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 344(a5)
	lui t0, 16
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 352(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 368(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 376(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 384(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 392(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 400(a5)
	addi a4, a5, 1024
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 0(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 8(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 16(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 24(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 32(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 40(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 48(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 56(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 64(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 72(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 80(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 88(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 96(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 104(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 112(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 120(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 128(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 136(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 144(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 152(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 160(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 168(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 184(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 192(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 200(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 208(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 216(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 224(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 232(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 240(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 248(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 256(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 264(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 272(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 288(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 296(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 304(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 312(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 320(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 328(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 336(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 344(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 352(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 368(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 392(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 400(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 408(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 416(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 456(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 464(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 472(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 480(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 488(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 496(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 504(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 528(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 544(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 552(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 560(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 568(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 576(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 584(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 592(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 600(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 608(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 616(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 624(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 632(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 640(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 648(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 656(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 664(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 672(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 680(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 688(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 696(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 704(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 712(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 720(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 728(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 736(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 744(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 752(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 760(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 768(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 776(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 784(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 792(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 800(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 808(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 816(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 824(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 832(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 840(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 848(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 856(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 864(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 872(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 880(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 888(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 896(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 904(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 912(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 920(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 928(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 936(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 944(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 952(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 960(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 968(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 976(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 984(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 992(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1000(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1008(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1016(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1024(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1032(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1040(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1048(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1056(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1064(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1072(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1080(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1088(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1096(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1104(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1112(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1120(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1128(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1136(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1144(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1152(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1160(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1168(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1176(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1184(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1192(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1200(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1208(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1216(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1224(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1232(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1240(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1248(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1256(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1264(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1272(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1280(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1288(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1296(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1304(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1312(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1320(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1328(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1336(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1344(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1352(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1360(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1368(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1376(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1384(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1392(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1400(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1408(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1416(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1424(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1432(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1440(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1448(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1456(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1464(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1472(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1480(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1488(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1496(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1504(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1512(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1520(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1528(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1536(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1544(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1552(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1560(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1568(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1576(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1584(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1592(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1600(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1608(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1616(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1624(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1632(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1640(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1648(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1656(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1664(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1672(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1680(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1688(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1696(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1704(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1712(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1720(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1728(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1736(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1744(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1752(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1760(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1768(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1776(a4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1784(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1792(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1800(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1808(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1816(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1824(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1832(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1840(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1848(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1856(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1864(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1872(a4)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1880(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1888(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1896(a4)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1904(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1912(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1920(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1928(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1936(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1944(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1952(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1960(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1968(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1976(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1984(a4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1992(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 2000(a4)
	lui t0, 1048560
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 2008(a4)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 2016(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 2024(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 2032(a4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 2040(a4)
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld s8, 400(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld s0, 896(a5)
	ld s1, 912(a5)
	ld s2, 928(a5)
	ld s3, 944(a5)
	ld s4, 960(a5)
	ld s5, 976(a5)
	ld s6, 992(a5)
	ld s7, 1008(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	ld s0, 904(a5)
	ld s1, 920(a5)
	ld s2, 936(a5)
	ld s3, 952(a5)
	ld s4, 968(a5)
	ld s5, 984(a5)
	ld s6, 1000(a5)
	ld s7, 1016(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 704(a5)
	sd s1, 712(a5)
	sd s2, 720(a5)
	sd s3, 728(a5)
	sd s4, 736(a5)
	sd s5, 744(a5)
	sd s6, 752(a5)
	sd s7, 760(a5)
	addi a4, a5, 2040
	addi a4, a4, 1032
	addi a3, a5, 1024
20:
	ld s0, 576(a5)
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 0(a3)
	xor s0, s0, t0
	ld s1, 584(a5)
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 8(a3)
	xor s1, s1, t0
	ld s2, 592(a5)
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 16(a3)
	xor s2, s2, t0
	ld s3, 600(a5)
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 24(a3)
	xor s3, s3, t0
	ld s4, 608(a5)
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 32(a3)
	xor s4, s4, t0
	ld s5, 616(a5)
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 40(a3)
	xor s5, s5, t0
	ld s6, 624(a5)
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 48(a3)
	xor s6, s6, t0
	ld s7, 632(a5)
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 56(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s3, 32
	slli t0, s3, 32
	xor t0, t0, a7
	xor t0, t0, s0
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 512(a5)
	xor t0, t0, t1
	sd t0, 512(a5)
	srli a7, s4, 32
	slli t0, s4, 32
	xor t0, t0, a7
	xor t0, t0, s1
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 520(a5)
	xor t0, t0, t1
	sd t0, 520(a5)
	srli a7, s5, 32
	slli t0, s5, 32
	xor t0, t0, a7
	xor t0, t0, s2
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 528(a5)
	xor t0, t0, t1
	sd t0, 528(a5)
	srli a7, s6, 32
	slli t0, s6, 32
	xor t0, t0, a7
	xor t0, t0, s3
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 536(a5)
	xor t0, t0, t1
	sd t0, 536(a5)
	srli a7, s7, 32
	slli t0, s7, 32
	xor t0, t0, a7
	xor t0, t0, s4
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 544(a5)
	xor t0, t0, t1
	sd t0, 544(a5)
	srli a7, s0, 16
	slli t0, s0, 48
	xor t0, t0, a7
	xor t0, t0, s5
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 552(a5)
	xor t0, t0, t1
	sd t0, 552(a5)
	srli a7, s1, 16
	slli t0, s1, 48
	xor t0, t0, a7
	xor t0, t0, s6
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 560(a5)
	xor t0, t0, t1
	sd t0, 560(a5)
	srli a7, s2, 16
	slli t0, s2, 48
	xor t0, t0, a7
	xor t0, t0, s7
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 568(a5)
	xor t0, t0, t1
	sd t0, 568(a5)
	ld s0, 640(a5)
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 64(a3)
	xor s0, s0, t0
	ld s1, 648(a5)
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 72(a3)
	xor s1, s1, t0
	ld s2, 656(a5)
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 80(a3)
	xor s2, s2, t0
	ld s3, 664(a5)
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 88(a3)
	xor s3, s3, t0
	ld s4, 672(a5)
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 96(a3)
	xor s4, s4, t0
	ld s5, 680(a5)
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 104(a3)
	xor s5, s5, t0
	ld s6, 688(a5)
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 112(a3)
	xor s6, s6, t0
	ld s7, 696(a5)
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 120(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s3, 32
	slli t0, s3, 32
	xor t0, t0, a7
	xor t0, t0, s0
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 576(a5)
	xor t0, t0, t1
	sd t0, 576(a5)
	srli a7, s4, 32
	slli t0, s4, 32
	xor t0, t0, a7
	xor t0, t0, s1
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 584(a5)
	xor t0, t0, t1
	sd t0, 584(a5)
	srli a7, s5, 32
	slli t0, s5, 32
	xor t0, t0, a7
	xor t0, t0, s2
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 592(a5)
	xor t0, t0, t1
	sd t0, 592(a5)
	srli a7, s6, 32
	slli t0, s6, 32
	xor t0, t0, a7
	xor t0, t0, s3
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 600(a5)
	xor t0, t0, t1
	sd t0, 600(a5)
	srli a7, s7, 32
	slli t0, s7, 32
	xor t0, t0, a7
	xor t0, t0, s4
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 608(a5)
	xor t0, t0, t1
	sd t0, 608(a5)
	srli a7, s0, 16
	slli t0, s0, 48
	xor t0, t0, a7
	xor t0, t0, s5
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 616(a5)
	xor t0, t0, t1
	sd t0, 616(a5)
	srli a7, s1, 16
	slli t0, s1, 48
	xor t0, t0, a7
	xor t0, t0, s6
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 624(a5)
	xor t0, t0, t1
	sd t0, 624(a5)
	srli a7, s2, 16
	slli t0, s2, 48
	xor t0, t0, a7
	xor t0, t0, s7
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 632(a5)
	xor t0, t0, t1
	sd t0, 632(a5)
	ld s0, 704(a5)
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 128(a3)
	xor s0, s0, t0
	ld s1, 712(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 136(a3)
	xor s1, s1, t0
	ld s2, 720(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 144(a3)
	xor s2, s2, t0
	ld s3, 728(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 152(a3)
	xor s3, s3, t0
	ld s4, 736(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 160(a3)
	xor s4, s4, t0
	ld s5, 744(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 168(a3)
	xor s5, s5, t0
	ld s6, 752(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 176(a3)
	xor s6, s6, t0
	ld s7, 760(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 184(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s3, 32
	slli t0, s3, 32
	xor t0, t0, a7
	xor t0, t0, s0
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 640(a5)
	xor t0, t0, t1
	sd t0, 640(a5)
	srli a7, s4, 32
	slli t0, s4, 32
	xor t0, t0, a7
	xor t0, t0, s1
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 648(a5)
	xor t0, t0, t1
	sd t0, 648(a5)
	srli a7, s5, 32
	slli t0, s5, 32
	xor t0, t0, a7
	xor t0, t0, s2
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 656(a5)
	xor t0, t0, t1
	sd t0, 656(a5)
	srli a7, s6, 32
	slli t0, s6, 32
	xor t0, t0, a7
	xor t0, t0, s3
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 664(a5)
	xor t0, t0, t1
	sd t0, 664(a5)
	srli a7, s7, 32
	slli t0, s7, 32
	xor t0, t0, a7
	xor t0, t0, s4
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 672(a5)
	xor t0, t0, t1
	sd t0, 672(a5)
	srli a7, s0, 16
	slli t0, s0, 48
	xor t0, t0, a7
	xor t0, t0, s5
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 680(a5)
	xor t0, t0, t1
	sd t0, 680(a5)
	srli a7, s1, 16
	slli t0, s1, 48
	xor t0, t0, a7
	xor t0, t0, s6
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 688(a5)
	xor t0, t0, t1
	sd t0, 688(a5)
	srli a7, s2, 16
	slli t0, s2, 48
	xor t0, t0, a7
	xor t0, t0, s7
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 696(a5)
	xor t0, t0, t1
	sd t0, 696(a5)
	ld s0, 512(a5)
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 192(a3)
	xor s0, s0, t0
	ld s1, 520(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 200(a3)
	xor s1, s1, t0
	ld s2, 528(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 208(a3)
	xor s2, s2, t0
	ld s3, 536(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 216(a3)
	xor s3, s3, t0
	ld s4, 544(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 224(a3)
	xor s4, s4, t0
	ld s5, 552(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 232(a3)
	xor s5, s5, t0
	ld s6, 560(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 240(a3)
	xor s6, s6, t0
	ld s7, 568(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 248(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s3, 32
	slli t0, s3, 32
	xor t0, t0, a7
	xor t0, t0, s0
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 704(a5)
	xor t0, t0, t1
	sd t0, 704(a5)
	srli a7, s4, 32
	slli t0, s4, 32
	xor t0, t0, a7
	xor t0, t0, s1
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 712(a5)
	xor t0, t0, t1
	sd t0, 712(a5)
	srli a7, s5, 32
	slli t0, s5, 32
	xor t0, t0, a7
	xor t0, t0, s2
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 720(a5)
	xor t0, t0, t1
	sd t0, 720(a5)
	srli a7, s6, 32
	slli t0, s6, 32
	xor t0, t0, a7
	xor t0, t0, s3
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 728(a5)
	xor t0, t0, t1
	sd t0, 728(a5)
	srli a7, s7, 32
	slli t0, s7, 32
	xor t0, t0, a7
	xor t0, t0, s4
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 736(a5)
	xor t0, t0, t1
	sd t0, 736(a5)
	srli a7, s0, 16
	slli t0, s0, 48
	xor t0, t0, a7
	xor t0, t0, s5
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 744(a5)
	xor t0, t0, t1
	sd t0, 744(a5)
	srli a7, s1, 16
	slli t0, s1, 48
	xor t0, t0, a7
	xor t0, t0, s6
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 752(a5)
	xor t0, t0, t1
	sd t0, 752(a5)
	srli a7, s2, 16
	slli t0, s2, 48
	xor t0, t0, a7
	xor t0, t0, s7
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 760(a5)
	xor t0, t0, t1
	sd t0, 760(a5)
	addi a3, a3, 256
	ld t3, 352(a5)
	ld t4, 336(a5)
	ld t5, 344(a5)
	ld t2, 640(a5)
	and t2, t2, t3
	ld t1, 648(a5)
	and t1, t1, t3
	slli t1, t1, 1
	xor t2, t2, t1
	ld t1, 656(a5)
	and t1, t1, t3
	slli t1, t1, 2
	xor t2, t2, t1
	ld t1, 664(a5)
	and t1, t1, t3
	slli t1, t1, 3
	xor t2, t2, t1
	ld t1, 672(a5)
	and t1, t1, t3
	slli t1, t1, 4
	xor t2, t2, t1
	ld t1, 680(a5)
	and t1, t1, t3
	slli t1, t1, 5
	xor t2, t2, t1
	ld t1, 688(a5)
	and t1, t1, t3
	slli t1, t1, 6
	xor t2, t2, t1
	ld t1, 696(a5)
	and t1, t1, t3
	slli t1, t1, 7
	xor t2, t2, t1
	srli t1, t2, 8
	xor t2, t2, t1
	and t2, t2, t4
	srli t1, t2, 16
	xor t2, t2, t1
	slli t2, t2, 32
	ld t0, 704(a5)
	and t0, t0, t3
	ld t1, 712(a5)
	and t1, t1, t3
	slli t1, t1, 1
	xor t0, t0, t1
	ld t1, 720(a5)
	and t1, t1, t3
	slli t1, t1, 2
	xor t0, t0, t1
	ld t1, 728(a5)
	and t1, t1, t3
	slli t1, t1, 3
	xor t0, t0, t1
	ld t1, 736(a5)
	and t1, t1, t3
	slli t1, t1, 4
	xor t0, t0, t1
	ld t1, 744(a5)
	and t1, t1, t3
	slli t1, t1, 5
	xor t0, t0, t1
	ld t1, 752(a5)
	and t1, t1, t3
	slli t1, t1, 6
	xor t0, t0, t1
	ld t1, 760(a5)
	and t1, t1, t3
	slli t1, t1, 7
	xor t0, t0, t1
	srli t1, t0, 8
	xor t0, t0, t1
	and t0, t0, t4
	srli t1, t0, 16
	xor t0, t0, t1
	and t0, t0, t5
	xor t0, t0, t2
	sd t0, 768(a5)
	ld t2, 512(a5)
	and t2, t2, t3
	ld t1, 520(a5)
	and t1, t1, t3
	slli t1, t1, 1
	xor t2, t2, t1
	ld t1, 528(a5)
	and t1, t1, t3
	slli t1, t1, 2
	xor t2, t2, t1
	ld t1, 536(a5)
	and t1, t1, t3
	slli t1, t1, 3
	xor t2, t2, t1
	ld t1, 544(a5)
	and t1, t1, t3
	slli t1, t1, 4
	xor t2, t2, t1
	ld t1, 552(a5)
	and t1, t1, t3
	slli t1, t1, 5
	xor t2, t2, t1
	ld t1, 560(a5)
	and t1, t1, t3
	slli t1, t1, 6
	xor t2, t2, t1
	ld t1, 568(a5)
	and t1, t1, t3
	slli t1, t1, 7
	xor t2, t2, t1
	srli t1, t2, 8
	xor t2, t2, t1
	and t2, t2, t4
	srli t1, t2, 16
	xor t2, t2, t1
	slli t2, t2, 32
	ld t0, 576(a5)
	and t0, t0, t3
	ld t1, 584(a5)
	and t1, t1, t3
	slli t1, t1, 1
	xor t0, t0, t1
	ld t1, 592(a5)
	and t1, t1, t3
	slli t1, t1, 2
	xor t0, t0, t1
	ld t1, 600(a5)
	and t1, t1, t3
	slli t1, t1, 3
	xor t0, t0, t1
	ld t1, 608(a5)
	and t1, t1, t3
	slli t1, t1, 4
	xor t0, t0, t1
	ld t1, 616(a5)
	and t1, t1, t3
	slli t1, t1, 5
	xor t0, t0, t1
	ld t1, 624(a5)
	and t1, t1, t3
	slli t1, t1, 6
	xor t0, t0, t1
	ld t1, 632(a5)
	and t1, t1, t3
	slli t1, t1, 7
	xor t0, t0, t1
	srli t1, t0, 8
	xor t0, t0, t1
	and t0, t0, t4
	srli t1, t0, 16
	xor t0, t0, t1
	and t0, t0, t5
	xor t0, t0, t2
	sd t0, 776(a5)
	ld t0, 776(a5)
	srli t1, t0, 56
	sb t1, 0(a1)
	srli t1, t0, 48
	sb t1, 1(a1)
	srli t1, t0, 40
	sb t1, 2(a1)
	srli t1, t0, 32
	sb t1, 3(a1)
	srli t1, t0, 24
	sb t1, 4(a1)
	srli t1, t0, 16
	sb t1, 5(a1)
	srli t1, t0, 8
	sb t1, 6(a1)
	srli t1, t0, 0
	sb t1, 7(a1)
	ld t0, 768(a5)
	srli t1, t0, 56
	sb t1, 8(a1)
	srli t1, t0, 48
	sb t1, 9(a1)
	srli t1, t0, 40
	sb t1, 10(a1)
	srli t1, t0, 32
	sb t1, 11(a1)
	srli t1, t0, 24
	sb t1, 12(a1)
	srli t1, t0, 16
	sb t1, 13(a1)
	srli t1, t0, 8
	sb t1, 14(a1)
	srli t1, t0, 0
	sb t1, 15(a1)
	addi a1, a1, 16
	sub t0, a3, a4
	bnez t0, 20b
	ret
	.option pop
