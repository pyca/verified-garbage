	ld 4, 8(15)
	ld 19, 8(3)
	ld 24, 8(14)
	ld 5, 16(15)
	ld 20, 16(3)
	ld 25, 16(14)
	ld 6, 24(15)
	ld 21, 24(3)
	ld 26, 24(14)
	ld 7, 32(15)
	ld 23, 32(3)
	ld 27, 32(14)
	mulhdu 8, 17, 4
	mulld 4, 17, 4
	mulhdu 28, 0, 19
	mulld 19, 0, 19
	mulhdu 9, 17, 5
	mulld 5, 17, 5
	mulhdu 29, 0, 20
	mulld 20, 0, 20
	mulhdu 10, 17, 6
	mulld 6, 17, 6
	mulhdu 30, 0, 21
	mulld 21, 0, 21
	mulhdu 11, 17, 7
	mulld 7, 17, 7
	mulhdu 31, 0, 23
	mulld 23, 0, 23
	addic 18, 18, -1
	adde 24, 24, 4
	adde 25, 25, 5
	adde 26, 26, 6
	adde 27, 27, 7
	addze 18, 1
	addic 22, 22, -1
	adde 24, 24, 12
	adde 25, 25, 8
	adde 26, 26, 9
	adde 27, 27, 10
	addze 22, 1
	addic 2, 2, -1
	adde 24, 24, 19
	adde 25, 25, 20
	adde 26, 26, 21
	adde 27, 27, 23
	addze 2, 1
	addic 13, 13, -1
	adde 24, 24, 16
	adde 25, 25, 28
	adde 26, 26, 29
	adde 27, 27, 30
	addze 13, 1
	mr 12, 11
	mr 16, 31
	std 24, 0(14)
	std 25, 8(14)
	std 26, 16(14)
	std 27, 24(14)
	addi 14, 14, 32
	addi 15, 15, 32
	addi 3, 3, 32
	addi 5, 5, -1
	cmpldi 5, 0
	bne .-1000
