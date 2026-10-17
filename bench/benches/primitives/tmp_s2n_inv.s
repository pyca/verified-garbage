stp x19, x20, [sp, #-16]! 
stp x21, x22, [sp, #-16]! 
sub sp, sp, #(16*8 +0) 
mov x20, x0
mov x10, #-19
mov x11, #-1
stp x10, x11, [sp, #0]
mov x12, #0x7FFFFFFFFFFFFFFF
stp x11, x12, [sp, #0 +2*8]
ldp x2, x3, [x1]
ldp x4, x5, [x1, #(2*8)]
mov x7, #19
lsr x6, x5, #63
madd x6, x7, x6, x7
adds x2, x2, x6
adcs x3, x3, xzr
adcs x4, x4, xzr
orr x5, x5, #0x8000000000000000
adcs x5, x5, xzr
csel x6, x7, xzr, cc
subs x2, x2, x6
sbcs x3, x3, xzr
sbcs x4, x4, xzr
sbc x5, x5, xzr
and x5, x5, #0x7fffffffffffffff
stp x2, x3, [sp, #(4*8)]
stp x4, x5, [sp, #(4*8)+2*8]
stp xzr, xzr, [sp, #(8*8)]
stp xzr, xzr, [sp, #(8*8)+2*8]
movz x10, 0x2099 
movk x10, 0x7502, lsl #16 
movk x10, 0x9e23, lsl #32 
movk x10, 0xa0f9, lsl #48
movz x11, 0x2595 
movk x11, 0x1d13, lsl #16 
movk x11, 0x8f3f, lsl #32 
movk x11, 0xa8c6, lsl #48
movz x12, 0x5242 
movk x12, 0x05ac, lsl #16 
movk x12, 0x8938, lsl #32 
movk x12, 0x6c6c, lsl #48
movz x13, 0x0615 
movk x13, 0x4177, lsl #16 
movk x13, 0x08b2, lsl #32 
movk x13, 0x2765, lsl #48
stp x10, x11, [sp, #(12*8)]
stp x12, x13, [sp, #(12*8)+2*8]
mov x21, #10
mov x22, #1
b Lbignum_inv_p25519_midloop
Lbignum_inv_p25519_loop:
cmp x10, xzr
csetm x14, mi
cneg x10, x10, mi
cmp x11, xzr
csetm x15, mi
cneg x11, x11, mi
cmp x12, xzr
csetm x16, mi
cneg x12, x12, mi
cmp x13, xzr
csetm x17, mi
cneg x13, x13, mi
and x0, x10, x14
and x1, x11, x15
add x9, x0, x1
and x0, x12, x16
and x1, x13, x17
add x19, x0, x1
ldr x7, [sp, #0]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x4, x9, x0
adc x2, xzr, x1
ldr x8, [sp, #(4*8)]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x4, x4, x0
adc x2, x2, x1
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x5, x19, x0
adc x3, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x5, x5, x0
adc x3, x3, x1
ldr x7, [sp, #0 +8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x2, x2, x0
adc x6, xzr, x1
ldr x8, [sp, #(4*8)+8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x2, x2, x0
adc x6, x6, x1
extr x4, x2, x4, #59
str x4, [sp, #0]
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x3, x3, x0
adc x4, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x3, x3, x0
adc x4, x4, x1
extr x5, x3, x5, #59
str x5, [sp, #(4*8)]
ldr x7, [sp, #0 +2*8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x6, x6, x0
adc x5, xzr, x1
ldr x8, [sp, #(4*8)+2*8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x6, x6, x0
adc x5, x5, x1
extr x2, x6, x2, #59
str x2, [sp, #0 +8]
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x4, x4, x0
adc x2, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x4, x4, x0
adc x2, x2, x1
extr x3, x4, x3, #59
str x3, [sp, #(4*8)+8]
ldr x7, [sp, #0 +3*8]
eor x1, x7, x14
asr x3, x1, #63
and x3, x3, x10
neg x3, x3
mul x0, x1, x10
umulh x1, x1, x10
adds x5, x5, x0
adc x3, x3, x1
ldr x8, [sp, #(4*8)+3*8]
eor x1, x8, x15
asr x0, x1, #63
and x0, x0, x11
sub x3, x3, x0
mul x0, x1, x11
umulh x1, x1, x11
adds x5, x5, x0
adc x3, x3, x1
extr x6, x5, x6, #59
str x6, [sp, #0 +2*8]
extr x5, x3, x5, #59
str x5, [sp, #0 +3*8]
eor x1, x7, x16
asr x5, x1, #63
and x5, x5, x12
neg x5, x5
mul x0, x1, x12
umulh x1, x1, x12
adds x2, x2, x0
adc x5, x5, x1
eor x1, x8, x17
asr x0, x1, #63
and x0, x0, x13
sub x5, x5, x0
mul x0, x1, x13
umulh x1, x1, x13
adds x2, x2, x0
adc x5, x5, x1
extr x4, x2, x4, #59
str x4, [sp, #(4*8)+2*8]
extr x2, x5, x2, #59
str x2, [sp, #(4*8)+3*8]
ldr x7, [sp, #(8*8)]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x4, x9, x0
adc x2, xzr, x1
ldr x8, [sp, #(12*8)]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x4, x4, x0
str x4, [sp, #(8*8)]
adc x2, x2, x1
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x5, x19, x0
adc x3, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x5, x5, x0
str x5, [sp, #(12*8)]
adc x3, x3, x1
ldr x7, [sp, #(8*8)+8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x2, x2, x0
adc x6, xzr, x1
ldr x8, [sp, #(12*8)+8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x2, x2, x0
str x2, [sp, #(8*8)+8]
adc x6, x6, x1
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x3, x3, x0
adc x4, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x3, x3, x0
str x3, [sp, #(12*8)+8]
adc x4, x4, x1
ldr x7, [sp, #(8*8)+2*8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x6, x6, x0
adc x5, xzr, x1
ldr x8, [sp, #(12*8)+2*8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x6, x6, x0
str x6, [sp, #(8*8)+2*8]
adc x5, x5, x1
eor x1, x7, x16
mul x0, x1, x12
umulh x1, x1, x12
adds x4, x4, x0
adc x2, xzr, x1
eor x1, x8, x17
mul x0, x1, x13
umulh x1, x1, x13
adds x4, x4, x0
str x4, [sp, #(12*8)+2*8]
adc x2, x2, x1
ldr x7, [sp, #(8*8)+3*8]
eor x1, x7, x14
and x3, x14, x10
neg x3, x3
mul x0, x1, x10
umulh x1, x1, x10
adds x5, x5, x0
adc x3, x3, x1
ldr x8, [sp, #(12*8)+3*8]
eor x1, x8, x15
and x0, x15, x11
sub x3, x3, x0
mul x0, x1, x11
umulh x1, x1, x11
adds x5, x5, x0
adc x3, x3, x1
extr x6, x3, x5, #63
ldp x0, x1, [sp, #(8*8)]
add x6, x6, x3, asr #63
mov x3, #19
mul x4, x6, x3
add x5, x5, x6, lsl #63
smulh x3, x6, x3
ldr x6, [sp, #(8*8)+2*8]
adds x0, x0, x4
adcs x1, x1, x3
asr x3, x3, #63
adcs x6, x6, x3
adc x5, x5, x3
stp x0, x1, [sp, #(8*8)]
stp x6, x5, [sp, #(8*8)+16]
eor x1, x7, x16
and x5, x16, x12
neg x5, x5
mul x0, x1, x12
umulh x1, x1, x12
adds x2, x2, x0
adc x5, x5, x1
eor x1, x8, x17
and x0, x17, x13
sub x5, x5, x0
mul x0, x1, x13
umulh x1, x1, x13
adds x2, x2, x0
adc x5, x5, x1
extr x6, x5, x2, #63
ldp x0, x1, [sp, #(12*8)]
add x6, x6, x5, asr #63
mov x5, #19
mul x4, x6, x5
add x2, x2, x6, lsl #63
smulh x5, x6, x5
ldr x3, [sp, #(12*8)+2*8]
adds x0, x0, x4
adcs x1, x1, x5
asr x5, x5, #63
adcs x3, x3, x5
adc x2, x2, x5
stp x0, x1, [sp, #(12*8)]
stp x3, x2, [sp, #(12*8)+16]
Lbignum_inv_p25519_midloop:
mov x1, x22
ldr x2, [sp, #0]
ldr x3, [sp, #(4*8)]
and x4, x2, #0xfffff 
orr x4, x4, #0xfffffe0000000000 
and x5, x3, #0xfffff 
orr x5, x5, #0xc000000000000000 
tst x5, #0x1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
asr x5, x5, #1 
add x8, x4, #0x100, lsl #12 
sbfx x8, x8, #21, #21 
mov x11, #0x100000 
add x11, x11, x11, lsl #21 
add x9, x4, x11 
asr x9, x9, #42 
add x10, x5, #0x100, lsl #12 
sbfx x10, x10, #21, #21 
add x11, x5, x11 
asr x11, x11, #42 
mul x6, x8, x2 
mul x7, x9, x3 
mul x2, x10, x2 
mul x3, x11, x3 
add x4, x6, x7 
add x5, x2, x3 
asr x2, x4, #20 
asr x3, x5, #20 
and x4, x2, #0xfffff 
orr x4, x4, #0xfffffe0000000000 
and x5, x3, #0xfffff 
orr x5, x5, #0xc000000000000000 
tst x5, #0x1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
asr x5, x5, #1 
add x12, x4, #0x100, lsl #12 
sbfx x12, x12, #21, #21 
mov x15, #0x100000 
add x15, x15, x15, lsl #21 
add x13, x4, x15 
asr x13, x13, #42 
add x14, x5, #0x100, lsl #12 
sbfx x14, x14, #21, #21 
add x15, x5, x15 
asr x15, x15, #42 
mul x6, x12, x2 
mul x7, x13, x3 
mul x2, x14, x2 
mul x3, x15, x3 
add x4, x6, x7 
add x5, x2, x3 
asr x2, x4, #20 
asr x3, x5, #20 
and x4, x2, #0xfffff 
orr x4, x4, #0xfffffe0000000000 
and x5, x3, #0xfffff 
orr x5, x5, #0xc000000000000000 
tst x5, #0x1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
mul x2, x12, x8 
mul x3, x12, x9 
mul x6, x14, x8 
mul x7, x14, x9 
madd x8, x13, x10, x2 
madd x9, x13, x11, x3 
madd x16, x15, x10, x6 
madd x17, x15, x11, x7 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
tst x5, #0x2 
asr x5, x5, #1 
csel x6, x4, xzr, ne 
ccmp x1, xzr, #0x8, ne 
cneg x1, x1, ge 
cneg x6, x6, ge 
csel x4, x5, x4, ge 
add x5, x5, x6 
add x1, x1, #0x2 
asr x5, x5, #1 
add x12, x4, #0x100, lsl #12 
sbfx x12, x12, #22, #21 
mov x15, #0x100000 
add x15, x15, x15, lsl #21 
add x13, x4, x15 
asr x13, x13, #43 
add x14, x5, #0x100, lsl #12 
sbfx x14, x14, #22, #21 
add x15, x5, x15 
asr x15, x15, #43 
mneg x2, x12, x8 
mneg x3, x12, x9 
mneg x4, x14, x8 
mneg x5, x14, x9 
msub x10, x13, x16, x2 
msub x11, x13, x17, x3 
msub x12, x15, x16, x4 
msub x13, x15, x17, x5
mov x22, x1
subs x21, x21, #1
bne Lbignum_inv_p25519_loop
ldr x0, [sp, #0]
ldr x1, [sp, #(4*8)]
mul x0, x0, x10
madd x1, x1, x11, x0
asr x0, x1, #63
cmp x10, xzr
csetm x14, mi
cneg x10, x10, mi
eor x14, x14, x0
cmp x11, xzr
csetm x15, mi
cneg x11, x11, mi
eor x15, x15, x0
cmp x12, xzr
csetm x16, mi
cneg x12, x12, mi
eor x16, x16, x0
cmp x13, xzr
csetm x17, mi
cneg x13, x13, mi
eor x17, x17, x0
and x0, x10, x14
and x1, x11, x15
add x9, x0, x1
ldr x7, [sp, #(8*8)]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x4, x9, x0
adc x2, xzr, x1
ldr x8, [sp, #(12*8)]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x4, x4, x0
str x4, [sp, #(8*8)]
adc x2, x2, x1
ldr x7, [sp, #(8*8)+8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x2, x2, x0
adc x6, xzr, x1
ldr x8, [sp, #(12*8)+8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x2, x2, x0
str x2, [sp, #(8*8)+8]
adc x6, x6, x1
ldr x7, [sp, #(8*8)+2*8]
eor x1, x7, x14
mul x0, x1, x10
umulh x1, x1, x10
adds x6, x6, x0
adc x5, xzr, x1
ldr x8, [sp, #(12*8)+2*8]
eor x1, x8, x15
mul x0, x1, x11
umulh x1, x1, x11
adds x6, x6, x0
str x6, [sp, #(8*8)+2*8]
adc x5, x5, x1
ldr x7, [sp, #(8*8)+3*8]
eor x1, x7, x14
and x3, x14, x10
neg x3, x3
mul x0, x1, x10
umulh x1, x1, x10
adds x5, x5, x0
adc x3, x3, x1
ldr x8, [sp, #(12*8)+3*8]
eor x1, x8, x15
and x0, x15, x11
sub x3, x3, x0
mul x0, x1, x11
umulh x1, x1, x11
adds x5, x5, x0
adc x3, x3, x1
extr x6, x3, x5, #63
ldp x0, x1, [sp, #(8*8)]
tst x3, x3
cinc x6, x6, pl
mov x3, #19
mul x4, x6, x3
add x5, x5, x6, lsl #63
smulh x6, x6, x3
ldr x2, [sp, #(8*8)+2*8]
adds x0, x0, x4
adcs x1, x1, x6
asr x6, x6, #63
adcs x2, x2, x6
adcs x5, x5, x6
csel x3, x3, xzr, mi
subs x0, x0, x3
sbcs x1, x1, xzr
sbcs x2, x2, xzr
sbc x5, x5, xzr
and x5, x5, #0x7fffffffffffffff
mov x4, x20
stp x0, x1, [x4]
stp x2, x5, [x4, #16]
add sp, sp, #(16*8 +0) 
ldp x21, x22, [sp], #16 
ldp x19, x20, [sp], #16 
ret 
