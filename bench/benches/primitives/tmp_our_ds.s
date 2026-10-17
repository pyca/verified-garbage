movz x7, #1, lsl #0
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
