ldr x1, [x0, #480]
ldr x2, [x0, #192]
ldr x3, [x0, #224]
movz x13, #0, lsl #0
sub x1, x13, x1
sub x1, x1, #1
movz x13, #32767, lsl #0
and x8, x2, x13
and x9, x3, x13
movz x16, #32768, lsl #16
add x8, x8, x16
movz x16, #32768, lsl #32
add x9, x9, x16
movz x12, #1, lsl #0
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
movz x13, #16384, lsl #16
movk x13, #8192, lsl #32
movk x13, #8192, lsl #48
movz x17, #16384, lsl #0
add x8, x8, x13
add x10, x10, x13
lsr x11, x8, #47
sub x11, x11, x17
lsl x8, x8, #17
lsr x8, x8, #48
sub x8, x8, x17
lsr x9, x10, #47
sub x9, x9, x17
lsl x10, x10, #17
lsr x10, x10, #48
sub x10, x10, x17
mul x13, x2, x8
madd x13, x3, x11, x13
mul x16, x2, x10
madd x16, x3, x9, x16
lsr x2, x13, #15
lsr x3, x16, #15
orr x4, x8, x8
orr x5, x11, x11
orr x6, x10, x10
orr x7, x9, x9
movz x13, #32767, lsl #0
and x8, x2, x13
and x9, x3, x13
movz x16, #32768, lsl #16
add x8, x8, x16
movz x16, #32768, lsl #32
add x9, x9, x16
movz x12, #1, lsl #0
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
movz x13, #16384, lsl #16
movk x13, #8192, lsl #32
movk x13, #8192, lsl #48
movz x17, #16384, lsl #0
add x8, x8, x13
add x10, x10, x13
lsr x11, x8, #47
sub x11, x11, x17
lsl x8, x8, #17
lsr x8, x8, #48
sub x8, x8, x17
lsr x9, x10, #47
sub x9, x9, x17
lsl x10, x10, #17
lsr x10, x10, #48
sub x10, x10, x17
mul x13, x2, x8
madd x13, x3, x11, x13
mul x16, x2, x10
madd x16, x3, x9, x16
lsr x2, x13, #15
lsr x3, x16, #15
mul x13, x8, x4
madd x13, x11, x6, x13
mul x16, x10, x4
madd x6, x9, x6, x16
mul x17, x8, x5
madd x17, x11, x7, x17
mul x16, x10, x5
madd x7, x9, x7, x16
orr x4, x13, x13
orr x5, x17, x17
movz x13, #32767, lsl #0
and x8, x2, x13
and x9, x3, x13
movz x16, #32768, lsl #16
add x8, x8, x16
movz x16, #32768, lsl #32
add x9, x9, x16
movz x12, #1, lsl #0
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
movz x13, #16384, lsl #16
movk x13, #8192, lsl #32
movk x13, #8192, lsl #48
movz x17, #16384, lsl #0
add x8, x8, x13
add x10, x10, x13
lsr x11, x8, #47
sub x11, x11, x17
lsl x8, x8, #17
lsr x8, x8, #48
sub x8, x8, x17
lsr x9, x10, #47
sub x9, x9, x17
lsl x10, x10, #17
lsr x10, x10, #48
sub x10, x10, x17
mul x13, x2, x8
madd x13, x3, x11, x13
mul x16, x2, x10
madd x16, x3, x9, x16
lsr x2, x13, #15
lsr x3, x16, #15
mul x13, x8, x4
madd x13, x11, x6, x13
mul x16, x10, x4
madd x6, x9, x6, x16
mul x17, x8, x5
madd x17, x11, x7, x17
mul x16, x10, x5
madd x7, x9, x7, x16
orr x4, x13, x13
orr x5, x17, x17
movz x13, #32767, lsl #0
and x8, x2, x13
and x9, x3, x13
movz x16, #32768, lsl #16
add x8, x8, x16
movz x16, #32768, lsl #32
add x9, x9, x16
movz x12, #1, lsl #0
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x10, x9, x8
sub x11, x9, x8
tst x9, x12
csel x10, x10, x9, ne
ccmp x1, #0, #0, ne
csel x10, x11, x10, mi
add x16, x9, x9
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
add x9, x10, x8
sub x11, x10, x8
tst x10, x12
csel x9, x9, x10, ne
ccmp x1, #0, #0, ne
csel x9, x11, x9, mi
add x16, x10, x10
add x8, x8, x8
csel x8, x16, x8, mi
add x13, x1, #4
sub x1, x1, #2
csneg x1, x1, x13, pl
add x12, x12, x12
movz x13, #16384, lsl #16
movk x13, #8192, lsl #32
movk x13, #8192, lsl #48
movz x17, #16384, lsl #0
add x8, x8, x13
add x9, x9, x13
lsr x11, x8, #47
sub x11, x11, x17
lsl x8, x8, #17
lsr x8, x8, #48
sub x8, x8, x17
lsr x10, x9, #47
sub x10, x10, x17
lsl x9, x9, #17
lsr x9, x9, #48
sub x9, x9, x17
mul x13, x8, x4
madd x13, x11, x6, x13
mul x16, x9, x4
madd x6, x10, x6, x16
mul x17, x8, x5
madd x17, x11, x7, x17
mul x16, x9, x5
madd x7, x10, x7, x16
orr x4, x13, x13
orr x5, x17, x17
movz x13, #0, lsl #0
sub x1, x13, x1
sub x1, x1, #1
str x1, [x0, #480]
movz x12, #0, lsl #0
lsr x14, x4, #63
sub x14, x12, x14
eor x4, x4, x14
sub x4, x4, x14
lsr x15, x5, #63
sub x15, x12, x15
eor x5, x5, x15
sub x5, x5, x15
lsr x16, x6, #63
sub x16, x12, x16
eor x6, x6, x16
sub x6, x6, x16
lsr x17, x7, #63
sub x17, x12, x17
eor x7, x7, x17
sub x7, x7, x17
and x8, x4, x14
and x9, x5, x15
add x13, x8, x9
and x8, x6, x16
and x9, x7, x17
add x19, x8, x9
ldr x8, [x0, #192]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x13, x9
adc x2, x12, x10
ldr x8, [x0, #224]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #320]
ldr x8, [x0, #200]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #232]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #328]
ldr x8, [x0, #208]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #240]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #336]
ldr x8, [x0, #216]
eor x8, x8, x14
lsr x3, x8, #63
sub x3, x12, x3
and x3, x3, x4
sub x3, x12, x3
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x3, x3, x10
ldr x8, [x0, #248]
eor x8, x8, x15
lsr x2, x8, #63
sub x2, x12, x2
and x2, x2, x5
sub x2, x12, x2
add x3, x3, x2
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x3, x3, x10
str x1, [x0, #344]
str x3, [x0, #352]
ldr x8, [x0, #192]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x19, x9
adc x2, x12, x10
ldr x8, [x0, #224]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #360]
ldr x8, [x0, #200]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #232]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #368]
ldr x8, [x0, #208]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #240]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #376]
ldr x8, [x0, #216]
eor x8, x8, x16
lsr x3, x8, #63
sub x3, x12, x3
and x3, x3, x6
sub x3, x12, x3
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x3, x3, x10
ldr x8, [x0, #248]
eor x8, x8, x17
lsr x2, x8, #63
sub x2, x12, x2
and x2, x2, x7
sub x2, x12, x2
add x3, x3, x2
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x3, x3, x10
str x1, [x0, #384]
str x3, [x0, #392]
ldr x8, [x0, #256]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x13, x9
adc x2, x12, x10
ldr x8, [x0, #288]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #400]
ldr x8, [x0, #264]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #296]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #408]
ldr x8, [x0, #272]
eor x8, x8, x14
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #304]
eor x8, x8, x15
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #416]
ldr x8, [x0, #280]
eor x8, x8, x14
and x3, x14, x4
sub x3, x12, x3
mul x9, x8, x4
umulh x10, x8, x4
adds x1, x2, x9
adc x3, x3, x10
ldr x8, [x0, #312]
eor x8, x8, x15
and x2, x15, x5
sub x2, x12, x2
add x3, x3, x2
mul x9, x8, x5
umulh x10, x8, x5
adds x1, x1, x9
adc x3, x3, x10
str x1, [x0, #424]
str x3, [x0, #432]
ldr x8, [x0, #256]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x19, x9
adc x2, x12, x10
ldr x8, [x0, #288]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #440]
ldr x8, [x0, #264]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #296]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #448]
ldr x8, [x0, #272]
eor x8, x8, x16
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x2, x12, x10
ldr x8, [x0, #304]
eor x8, x8, x17
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x2, x2, x10
str x1, [x0, #456]
ldr x8, [x0, #280]
eor x8, x8, x16
and x3, x16, x6
sub x3, x12, x3
mul x9, x8, x6
umulh x10, x8, x6
adds x1, x2, x9
adc x3, x3, x10
ldr x8, [x0, #312]
eor x8, x8, x17
and x2, x17, x7
sub x2, x12, x2
add x3, x3, x2
mul x9, x8, x7
umulh x10, x8, x7
adds x1, x1, x9
adc x3, x3, x10
str x1, [x0, #464]
str x3, [x0, #472]
ldr x1, [x0, #320]
ldr x2, [x0, #328]
ldr x3, [x0, #336]
ldr x8, [x0, #344]
ldr x9, [x0, #352]
extr x1, x2, x1, #59
extr x2, x3, x2, #59
extr x3, x8, x3, #59
extr x8, x9, x8, #59
str x1, [x0, #192]
str x2, [x0, #200]
str x3, [x0, #208]
str x8, [x0, #216]
ldr x1, [x0, #360]
ldr x2, [x0, #368]
ldr x3, [x0, #376]
ldr x8, [x0, #384]
ldr x9, [x0, #392]
extr x1, x2, x1, #59
extr x2, x3, x2, #59
extr x3, x8, x3, #59
extr x8, x9, x8, #59
str x1, [x0, #224]
str x2, [x0, #232]
str x3, [x0, #240]
str x8, [x0, #248]
movz x13, #19, lsl #0
ldr x1, [x0, #400]
ldr x2, [x0, #408]
ldr x3, [x0, #416]
ldr x8, [x0, #424]
ldr x9, [x0, #432]
extr x10, x9, x8, #63
lsr x11, x9, #63
sub x10, x10, x11
lsl x11, x10, #63
add x8, x8, x11
lsr x14, x10, #63
sub x14, x12, x14
mul x9, x10, x13
umulh x11, x10, x13
and x15, x14, x13
sub x11, x11, x15
adds x1, x1, x9
adcs x2, x2, x11
adcs x3, x3, x14
adc x8, x8, x14
str x1, [x0, #256]
str x2, [x0, #264]
str x3, [x0, #272]
str x8, [x0, #280]
ldr x1, [x0, #440]
ldr x2, [x0, #448]
ldr x3, [x0, #456]
ldr x8, [x0, #464]
ldr x9, [x0, #472]
extr x10, x9, x8, #63
lsr x11, x9, #63
sub x10, x10, x11
lsl x11, x10, #63
add x8, x8, x11
lsr x14, x10, #63
sub x14, x12, x14
mul x9, x10, x13
umulh x11, x10, x13
and x15, x14, x13
sub x11, x11, x15
adds x1, x1, x9
adcs x2, x2, x11
adcs x3, x3, x14
adc x8, x8, x14
str x1, [x0, #288]
str x2, [x0, #296]
str x3, [x0, #304]
str x8, [x0, #312]
ldr x19, [x0, #488]
sub x19, x19, #1
str x19, [x0, #488]