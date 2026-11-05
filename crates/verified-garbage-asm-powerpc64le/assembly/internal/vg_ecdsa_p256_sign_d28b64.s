// The functions of `src/internal/vg_ecdsa_p256_sign_d28b64.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign_d28b64:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 260(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 264(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 268(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 284(%r11)
	addi %r11, %r1, 0
	lis %r9, 257
	ori %r9, %r9, 257
	li %r10, 0
	stw %r9, 96(%r11)
	stw %r10, 32(%r11)
	stw %r9, 100(%r11)
	stw %r10, 36(%r11)
	stw %r9, 104(%r11)
	stw %r10, 40(%r11)
	stw %r9, 108(%r11)
	stw %r10, 44(%r11)
	stw %r9, 112(%r11)
	stw %r10, 48(%r11)
	stw %r9, 116(%r11)
	stw %r10, 52(%r11)
	stw %r9, 120(%r11)
	stw %r10, 56(%r11)
	stw %r9, 124(%r11)
	stw %r10, 60(%r11)
	stw %r9, 128(%r11)
	stw %r10, 64(%r11)
	stw %r9, 132(%r11)
	stw %r10, 68(%r11)
	stw %r9, 136(%r11)
	stw %r10, 72(%r11)
	stw %r9, 140(%r11)
	stw %r10, 76(%r11)
	stw %r9, 144(%r11)
	stw %r10, 80(%r11)
	stw %r9, 148(%r11)
	stw %r10, 84(%r11)
	stw %r9, 152(%r11)
	stw %r10, 88(%r11)
	stw %r9, 156(%r11)
	stw %r10, 92(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2345(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 93
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 157
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 1
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2345(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 93
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 157
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
20:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 424(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 428(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 452(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p256_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 21f
	li %r12, 0
	b 22f
21:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 29
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 93
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r12, 1
22:
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	addi %r11, %r1, 0
	li %r12, 0
	std %r12, 32(%r11)
	std %r12, 40(%r11)
	std %r12, 48(%r11)
	std %r12, 56(%r11)
	std %r12, 64(%r11)
	std %r12, 72(%r11)
	std %r12, 80(%r11)
	std %r12, 88(%r11)
	std %r12, 96(%r11)
	std %r12, 104(%r11)
	std %r12, 112(%r11)
	std %r12, 120(%r11)
	std %r12, 128(%r11)
	std %r12, 136(%r11)
	std %r12, 144(%r11)
	std %r12, 152(%r11)
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	std %r12, 256(%r11)
	std %r12, 264(%r11)
	std %r12, 272(%r11)
	std %r12, 280(%r11)
	std %r12, 288(%r11)
	std %r12, 296(%r11)
	std %r12, 304(%r11)
	std %r12, 312(%r11)
	std %r12, 320(%r11)
	std %r12, 328(%r11)
	std %r12, 336(%r11)
	std %r12, 344(%r11)
	std %r12, 352(%r11)
	std %r12, 360(%r11)
	std %r12, 368(%r11)
	std %r12, 376(%r11)
	std %r12, 384(%r11)
	std %r12, 392(%r11)
	std %r12, 400(%r11)
	std %r12, 408(%r11)
	std %r12, 416(%r11)
	std %r12, 424(%r11)
	std %r12, 432(%r11)
	std %r12, 440(%r11)
	std %r12, 448(%r11)
	std %r12, 456(%r11)
	std %r12, 464(%r11)
	std %r12, 472(%r11)
	std %r12, 480(%r11)
	std %r12, 488(%r11)
	std %r12, 496(%r11)
	std %r12, 504(%r11)
	std %r12, 512(%r11)
	std %r12, 520(%r11)
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
