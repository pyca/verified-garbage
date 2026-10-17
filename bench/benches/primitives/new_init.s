str x1, [x0, #496]
movz x12, #0, lsl #0
movz x6, #19, lsl #0
movz x7, #65535, lsl #0
movk x7, #65535, lsl #16
movk x7, #65535, lsl #32
movk x7, #32767, lsl #48
ldr x2, [x0, #128]
ldr x3, [x0, #136]
ldr x4, [x0, #144]
ldr x5, [x0, #152]
lsr x8, x5, #63
and x5, x5, x7
mul x8, x8, x6
adds x2, x2, x8
adcs x3, x3, x12
adcs x4, x4, x12
adc x5, x5, x12
adds x8, x2, x6
adcs x9, x3, x12
adcs x10, x4, x12
adc x11, x5, x12
lsr x13, x11, #63
and x11, x11, x7
sub x13, x12, x13
eor x8, x8, x2
and x8, x8, x13
eor x2, x2, x8
eor x9, x9, x3
and x9, x9, x13
eor x3, x3, x9
eor x10, x10, x4
and x10, x10, x13
eor x4, x4, x10
eor x11, x11, x5
and x11, x11, x13
eor x5, x5, x11
str x2, [x0, #224]
str x3, [x0, #232]
str x4, [x0, #240]
str x5, [x0, #248]
movz x2, #65517, lsl #0
movk x2, #65535, lsl #16
movk x2, #65535, lsl #32
movk x2, #65535, lsl #48
str x2, [x0, #192]
movz x2, #65535, lsl #0
movk x2, #65535, lsl #16
movk x2, #65535, lsl #32
movk x2, #65535, lsl #48
str x2, [x0, #200]
movz x2, #65535, lsl #0
movk x2, #65535, lsl #16
movk x2, #65535, lsl #32
movk x2, #65535, lsl #48
str x2, [x0, #208]
movz x2, #65535, lsl #0
movk x2, #65535, lsl #16
movk x2, #65535, lsl #32
movk x2, #32767, lsl #48
str x2, [x0, #216]
str x12, [x0, #256]
str x12, [x0, #264]
str x12, [x0, #272]
str x12, [x0, #280]
movz x2, #8345, lsl #0
movk x2, #29954, lsl #16
movk x2, #40483, lsl #32
movk x2, #41209, lsl #48
str x2, [x0, #288]
movz x2, #9621, lsl #0
movk x2, #7443, lsl #16
movk x2, #36671, lsl #32
movk x2, #43206, lsl #48
str x2, [x0, #296]
movz x2, #21058, lsl #0
movk x2, #1452, lsl #16
movk x2, #35128, lsl #32
movk x2, #27756, lsl #48
str x2, [x0, #304]
movz x2, #1557, lsl #0
movk x2, #16759, lsl #16
movk x2, #2226, lsl #32
movk x2, #10085, lsl #48
str x2, [x0, #312]
movz x1, #1, lsl #0
str x1, [x0, #480]
movz x19, #10, lsl #0
str x19, [x0, #488]