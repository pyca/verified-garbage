// The functions of `src/internal/vg_triple_des_transpose.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_transpose:
	addi %r25, %r10, 512
	ld %r21, 0(%r25)
	ld %r22, 8(%r25)
	ld %r23, 16(%r25)
	ld %r12, 0(%r10)
	ld %r14, 64(%r10)
	ld %r15, 128(%r10)
	ld %r16, 192(%r10)
	ld %r17, 256(%r10)
	ld %r18, 320(%r10)
	ld %r19, 384(%r10)
	ld %r20, 448(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 64(%r10)
	std %r15, 128(%r10)
	std %r16, 192(%r10)
	std %r17, 256(%r10)
	std %r18, 320(%r10)
	std %r19, 384(%r10)
	std %r20, 448(%r10)
	ld %r12, 8(%r10)
	ld %r14, 72(%r10)
	ld %r15, 136(%r10)
	ld %r16, 200(%r10)
	ld %r17, 264(%r10)
	ld %r18, 328(%r10)
	ld %r19, 392(%r10)
	ld %r20, 456(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 8(%r10)
	std %r14, 72(%r10)
	std %r15, 136(%r10)
	std %r16, 200(%r10)
	std %r17, 264(%r10)
	std %r18, 328(%r10)
	std %r19, 392(%r10)
	std %r20, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 80(%r10)
	ld %r15, 144(%r10)
	ld %r16, 208(%r10)
	ld %r17, 272(%r10)
	ld %r18, 336(%r10)
	ld %r19, 400(%r10)
	ld %r20, 464(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 16(%r10)
	std %r14, 80(%r10)
	std %r15, 144(%r10)
	std %r16, 208(%r10)
	std %r17, 272(%r10)
	std %r18, 336(%r10)
	std %r19, 400(%r10)
	std %r20, 464(%r10)
	ld %r12, 24(%r10)
	ld %r14, 88(%r10)
	ld %r15, 152(%r10)
	ld %r16, 216(%r10)
	ld %r17, 280(%r10)
	ld %r18, 344(%r10)
	ld %r19, 408(%r10)
	ld %r20, 472(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 24(%r10)
	std %r14, 88(%r10)
	std %r15, 152(%r10)
	std %r16, 216(%r10)
	std %r17, 280(%r10)
	std %r18, 344(%r10)
	std %r19, 408(%r10)
	std %r20, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 96(%r10)
	ld %r15, 160(%r10)
	ld %r16, 224(%r10)
	ld %r17, 288(%r10)
	ld %r18, 352(%r10)
	ld %r19, 416(%r10)
	ld %r20, 480(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 32(%r10)
	std %r14, 96(%r10)
	std %r15, 160(%r10)
	std %r16, 224(%r10)
	std %r17, 288(%r10)
	std %r18, 352(%r10)
	std %r19, 416(%r10)
	std %r20, 480(%r10)
	ld %r12, 40(%r10)
	ld %r14, 104(%r10)
	ld %r15, 168(%r10)
	ld %r16, 232(%r10)
	ld %r17, 296(%r10)
	ld %r18, 360(%r10)
	ld %r19, 424(%r10)
	ld %r20, 488(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 40(%r10)
	std %r14, 104(%r10)
	std %r15, 168(%r10)
	std %r16, 232(%r10)
	std %r17, 296(%r10)
	std %r18, 360(%r10)
	std %r19, 424(%r10)
	std %r20, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 112(%r10)
	ld %r15, 176(%r10)
	ld %r16, 240(%r10)
	ld %r17, 304(%r10)
	ld %r18, 368(%r10)
	ld %r19, 432(%r10)
	ld %r20, 496(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 48(%r10)
	std %r14, 112(%r10)
	std %r15, 176(%r10)
	std %r16, 240(%r10)
	std %r17, 304(%r10)
	std %r18, 368(%r10)
	std %r19, 432(%r10)
	std %r20, 496(%r10)
	ld %r12, 56(%r10)
	ld %r14, 120(%r10)
	ld %r15, 184(%r10)
	ld %r16, 248(%r10)
	ld %r17, 312(%r10)
	ld %r18, 376(%r10)
	ld %r19, 440(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 56(%r10)
	std %r14, 120(%r10)
	std %r15, 184(%r10)
	std %r16, 248(%r10)
	std %r17, 312(%r10)
	std %r18, 376(%r10)
	std %r19, 440(%r10)
	std %r20, 504(%r10)
	ld %r21, 24(%r25)
	ld %r22, 32(%r25)
	ld %r23, 40(%r25)
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	ld %r15, 16(%r10)
	ld %r16, 24(%r10)
	ld %r17, 32(%r10)
	ld %r18, 40(%r10)
	ld %r19, 48(%r10)
	ld %r20, 56(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 8(%r10)
	std %r15, 16(%r10)
	std %r16, 24(%r10)
	std %r17, 32(%r10)
	std %r18, 40(%r10)
	std %r19, 48(%r10)
	std %r20, 56(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	ld %r15, 80(%r10)
	ld %r16, 88(%r10)
	ld %r17, 96(%r10)
	ld %r18, 104(%r10)
	ld %r19, 112(%r10)
	ld %r20, 120(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 64(%r10)
	std %r14, 72(%r10)
	std %r15, 80(%r10)
	std %r16, 88(%r10)
	std %r17, 96(%r10)
	std %r18, 104(%r10)
	std %r19, 112(%r10)
	std %r20, 120(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	ld %r15, 144(%r10)
	ld %r16, 152(%r10)
	ld %r17, 160(%r10)
	ld %r18, 168(%r10)
	ld %r19, 176(%r10)
	ld %r20, 184(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 128(%r10)
	std %r14, 136(%r10)
	std %r15, 144(%r10)
	std %r16, 152(%r10)
	std %r17, 160(%r10)
	std %r18, 168(%r10)
	std %r19, 176(%r10)
	std %r20, 184(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	ld %r15, 208(%r10)
	ld %r16, 216(%r10)
	ld %r17, 224(%r10)
	ld %r18, 232(%r10)
	ld %r19, 240(%r10)
	ld %r20, 248(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 192(%r10)
	std %r14, 200(%r10)
	std %r15, 208(%r10)
	std %r16, 216(%r10)
	std %r17, 224(%r10)
	std %r18, 232(%r10)
	std %r19, 240(%r10)
	std %r20, 248(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	ld %r15, 272(%r10)
	ld %r16, 280(%r10)
	ld %r17, 288(%r10)
	ld %r18, 296(%r10)
	ld %r19, 304(%r10)
	ld %r20, 312(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 256(%r10)
	std %r14, 264(%r10)
	std %r15, 272(%r10)
	std %r16, 280(%r10)
	std %r17, 288(%r10)
	std %r18, 296(%r10)
	std %r19, 304(%r10)
	std %r20, 312(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	ld %r15, 336(%r10)
	ld %r16, 344(%r10)
	ld %r17, 352(%r10)
	ld %r18, 360(%r10)
	ld %r19, 368(%r10)
	ld %r20, 376(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 320(%r10)
	std %r14, 328(%r10)
	std %r15, 336(%r10)
	std %r16, 344(%r10)
	std %r17, 352(%r10)
	std %r18, 360(%r10)
	std %r19, 368(%r10)
	std %r20, 376(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	ld %r15, 400(%r10)
	ld %r16, 408(%r10)
	ld %r17, 416(%r10)
	ld %r18, 424(%r10)
	ld %r19, 432(%r10)
	ld %r20, 440(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 384(%r10)
	std %r14, 392(%r10)
	std %r15, 400(%r10)
	std %r16, 408(%r10)
	std %r17, 416(%r10)
	std %r18, 424(%r10)
	std %r19, 432(%r10)
	std %r20, 440(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	ld %r15, 464(%r10)
	ld %r16, 472(%r10)
	ld %r17, 480(%r10)
	ld %r18, 488(%r10)
	ld %r19, 496(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 448(%r10)
	std %r14, 456(%r10)
	std %r15, 464(%r10)
	std %r16, 472(%r10)
	std %r17, 480(%r10)
	std %r18, 488(%r10)
	std %r19, 496(%r10)
	std %r20, 504(%r10)
	lis %r11, -1
	ori %r11, %r11, 65535
	blr
