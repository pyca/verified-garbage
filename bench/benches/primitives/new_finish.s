movz x12, #0, lsl #0
movz x6, #19, lsl #0
movz x7, #65535, lsl #0
movk x7, #65535, lsl #16
movk x7, #65535, lsl #32
movk x7, #32767, lsl #48
ldr x2, [x0, #256]
ldr x3, [x0, #264]
ldr x4, [x0, #272]
ldr x5, [x0, #280]
lsr x8, x5, #63
and x5, x5, x7
mul x8, x8, x6
adds x2, x2, x8
adcs x3, x3, x12
adcs x4, x4, x12
adc x5, x5, x12
movz x9, #65498, lsl #0
movk x9, #65535, lsl #16
movk x9, #65535, lsl #32
movk x9, #65535, lsl #48
movz x10, #65535, lsl #0
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs x8, x9, x2
sbcs x9, x10, x3
sbcs x11, x10, x4
sbc x10, x10, x5
ldr x13, [x0, #216]
lsr x13, x13, #63
sub x13, x12, x13
eor x8, x8, x2
and x8, x8, x13
eor x2, x2, x8
eor x9, x9, x3
and x9, x9, x13
eor x3, x3, x9
eor x11, x11, x4
and x11, x11, x13
eor x4, x4, x11
eor x10, x10, x5
and x10, x10, x13
eor x5, x5, x10
str x2, [x0, #544]
str x3, [x0, #552]
str x4, [x0, #560]
str x5, [x0, #568]
ldr x1, [x0, #496]