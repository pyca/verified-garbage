	ld 19, 8(14)
	ld 20, 8(15)
	mulld 12, 17, 20
	mulhdu 20, 17, 20
	addc 19, 19, 12
	addze 20, 20
	addc 19, 19, 18
	addze 18, 20
	ld 20, 8(3)
	mulld 12, 0, 20
	mulhdu 20, 0, 20
	addc 12, 12, 19
	addze 20, 20
	addc 12, 12, 22
	addze 22, 20
	std 12, 0(14)
	ld 19, 16(14)
	ld 20, 16(15)
	mulld 12, 17, 20
	mulhdu 20, 17, 20
	addc 19, 19, 12
	addze 20, 20
	addc 19, 19, 18
	addze 18, 20
	ld 20, 16(3)
	mulld 12, 0, 20
	mulhdu 20, 0, 20
	addc 12, 12, 19
	addze 20, 20
	addc 12, 12, 22
	addze 22, 20
	std 12, 8(14)
	ld 19, 24(14)
	ld 20, 24(15)
	mulld 12, 17, 20
	mulhdu 20, 17, 20
	addc 19, 19, 12
	addze 20, 20
	addc 19, 19, 18
	addze 18, 20
	ld 20, 24(3)
	mulld 12, 0, 20
	mulhdu 20, 0, 20
	addc 12, 12, 19
	addze 20, 20
	addc 12, 12, 22
	addze 22, 20
	std 12, 16(14)
	ld 19, 32(14)
	ld 20, 32(15)
	mulld 12, 17, 20
	mulhdu 20, 17, 20
	addc 19, 19, 12
	addze 20, 20
	addc 19, 19, 18
	addze 18, 20
	ld 20, 32(3)
	mulld 12, 0, 20
	mulhdu 20, 0, 20
	addc 12, 12, 19
	addze 20, 20
	addc 12, 12, 22
	addze 22, 20
	std 12, 24(14)
	addi 14, 14, 32
	addi 15, 15, 32
	addi 3, 3, 32
	addi 16, 16, -1
	cmpldi 16, 0
	bne .-1000
