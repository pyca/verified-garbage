movz x7, #0, lsl #0
ldr x3, [x0, #576]
ldr x4, [x0, #584]
ldr x5, [x0, #592]
ldr x6, [x0, #600]
mul x8, x3, x4
umulh x9, x3, x4
mul x1, x3, x5
umulh x2, x3, x5
mul x10, x3, x6
umulh x11, x3, x6
mul x14, x4, x6
umulh x15, x4, x6
mul x12, x5, x6
umulh x13, x5, x6
mul x16, x4, x5
umulh x17, x4, x5
adds x9, x9, x1
adcs x10, x10, x2
adcs x11, x11, x14
adcs x12, x12, x15
adc x13, x13, x7
adds x10, x10, x16
adcs x11, x11, x17
adcs x12, x12, x7
adc x13, x13, x7
adds x8, x8, x8
adcs x9, x9, x9
adcs x10, x10, x10
adcs x11, x11, x11
adcs x12, x12, x12
adcs x13, x13, x13
adc x14, x7, x7
mul x15, x3, x3
umulh x1, x3, x3
mul x2, x4, x4
umulh x16, x4, x4
mul x17, x5, x5
umulh x3, x5, x5
mul x4, x6, x6
umulh x6, x6, x6
adds x8, x8, x1
adcs x9, x9, x2
adcs x10, x10, x16
adcs x11, x11, x17
adcs x12, x12, x3
adcs x13, x13, x4
adc x14, x14, x6
lsl x1, x15, #32
sub x4, x15, x1
adds x8, x8, x1
extr x2, x8, x15, #32
adcs x9, x9, x2
extr x3, x9, x8, #32
adcs x10, x10, x3
add x5, x10, x4
extr x6, x5, x9, #32
lsr x16, x5, #32
adcs x11, x11, x6
adcs x12, x12, x16
adcs x13, x13, x7
adc x14, x14, x7
subs x1, x15, x1
sbcs x15, x15, x2
sbcs x2, x8, x3
sbcs x3, x9, x6
sbc x1, x5, x16
adds x4, x10, x4
adcs x15, x15, x8
adcs x2, x2, x9
adcs x3, x3, x5
adc x1, x1, x7
adds x8, x11, x15
adcs x9, x12, x2
adcs x10, x13, x3
adcs x11, x14, x1
adc x12, x7, x7
movz x2, #1, lsl #0
adds x1, x8, x2
ldr x2, [x0, #72]
sbcs x3, x9, x2
sbcs x4, x10, x7
ldr x2, [x0, #88]
sbcs x5, x11, x2
sbcs x2, x12, x7
csel x8, x1, x8, hs
csel x9, x3, x9, hs
csel x10, x4, x10, hs
csel x11, x5, x11, hs
str x8, [x0, #800]
str x9, [x0, #808]
str x10, [x0, #816]
str x11, [x0, #824]
