module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! # The field operations of s2n-bignum's AArch64 X25519 ladder

The field arithmetic of `curve25519_x25519_byte_alt`
(s2n-bignum, `arm/curve25519/curve25519_x25519_byte_alt.S` as of commit
`c9ae3219055955cd39951e46953f6cdc97d98c19` of
<https://github.com/awslabs/s2n-bignum>, the copy AWS-LC 5.7.0 imports;
Apache-2.0 OR ISC OR MIT-0, used here under MIT-0): its macros `mul_4`, `sqr_4`, `add_twice4`,
`sub_twice4`, `cmadd_4` and `mux_4`, instruction for instruction, on field
elements of four little-endian words in the workspace at `x0` instead of on
the stack. Their order and register allocation are s2n-bignum's; their proofs
are this library's.

Three instructions of the original are written as the model has them: `xzr`
is x17, which holds zero; `cset r, cs` is `adc r, x17, x17`; and `cmn r, r`
followed by `and r, r, #0x7fffffffffffffff` is `adds t, r, r` then
`lsr r, t, #1` for a register `t` that is not live (the same flags, and `r`
without its bit 63). `mux_4`'s x0–x3 are x4–x7, as x0 is the workspace.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Alt
open VG.AArch64

/-- `mul_4`: the product of the field elements at `a` and `b`, below `2·p`,
into `o` (which may be either). Schoolbook rows of `mul`/`umulh` on x3–x16,
then 38 times the high half folded in, then the bits from 255 up times 19
(`2²⁵⁵ = 19` modulo p). -/
def mul4 (o a b : Nat) : List Instr :=
  [.ldp .x3 .x4 .x0 a,
    .ldp .x7 .x8 .x0 b,
    .mul .x .x12 .x3 .x7,
    .umulh .x13 .x3 .x7,
    .mul .x .x11 .x3 .x8,
    .umulh .x14 .x3 .x8,
    .adds .x .x13 .x13 .x11,
    .ldp .x9 .x10 .x0 (b + 16),
    .mul .x .x11 .x3 .x9,
    .umulh .x15 .x3 .x9,
    .adcs .x .x14 .x14 .x11,
    .mul .x .x11 .x3 .x10,
    .umulh .x16 .x3 .x10,
    .adcs .x .x15 .x15 .x11,
    .adc .x .x16 .x16 .x17,
    .ldp .x5 .x6 .x0 (a + 16),
    .mul .x .x11 .x4 .x7,
    .adds .x .x13 .x13 .x11,
    .mul .x .x11 .x4 .x8,
    .adcs .x .x14 .x14 .x11,
    .mul .x .x11 .x4 .x9,
    .adcs .x .x15 .x15 .x11,
    .mul .x .x11 .x4 .x10,
    .adcs .x .x16 .x16 .x11,
    .umulh .x3 .x4 .x10,
    .adc .x .x3 .x3 .x17,
    .umulh .x11 .x4 .x7,
    .adds .x .x14 .x14 .x11,
    .umulh .x11 .x4 .x8,
    .adcs .x .x15 .x15 .x11,
    .umulh .x11 .x4 .x9,
    .adcs .x .x16 .x16 .x11,
    .adc .x .x3 .x3 .x17,
    .mul .x .x11 .x5 .x7,
    .adds .x .x14 .x14 .x11,
    .mul .x .x11 .x5 .x8,
    .adcs .x .x15 .x15 .x11,
    .mul .x .x11 .x5 .x9,
    .adcs .x .x16 .x16 .x11,
    .mul .x .x11 .x5 .x10,
    .adcs .x .x3 .x3 .x11,
    .umulh .x4 .x5 .x10,
    .adc .x .x4 .x4 .x17,
    .umulh .x11 .x5 .x7,
    .adds .x .x15 .x15 .x11,
    .umulh .x11 .x5 .x8,
    .adcs .x .x16 .x16 .x11,
    .umulh .x11 .x5 .x9,
    .adcs .x .x3 .x3 .x11,
    .adc .x .x4 .x4 .x17,
    .mul .x .x11 .x6 .x7,
    .adds .x .x15 .x15 .x11,
    .mul .x .x11 .x6 .x8,
    .adcs .x .x16 .x16 .x11,
    .mul .x .x11 .x6 .x9,
    .adcs .x .x3 .x3 .x11,
    .mul .x .x11 .x6 .x10,
    .adcs .x .x4 .x4 .x11,
    .umulh .x5 .x6 .x10,
    .adc .x .x5 .x5 .x17,
    .umulh .x11 .x6 .x7,
    .adds .x .x16 .x16 .x11,
    .umulh .x11 .x6 .x8,
    .adcs .x .x3 .x3 .x11,
    .umulh .x11 .x6 .x9,
    .adcs .x .x4 .x4 .x11,
    .adc .x .x5 .x5 .x17,
    .movz .w .x7 38 0,
    .mul .x .x11 .x7 .x16,
    .umulh .x9 .x7 .x16,
    .adds .x .x12 .x12 .x11,
    .mul .x .x11 .x7 .x3,
    .umulh .x3 .x7 .x3,
    .adcs .x .x13 .x13 .x11,
    .mul .x .x11 .x7 .x4,
    .umulh .x4 .x7 .x4,
    .adcs .x .x14 .x14 .x11,
    .mul .x .x11 .x7 .x5,
    .umulh .x5 .x7 .x5,
    .adcs .x .x15 .x15 .x11,
    .adc .x .x16 .x17 .x17,
    .adds .x .x15 .x15 .x4,
    .adc .x .x16 .x16 .x5,
    .adds .x .x11 .x15 .x15,
    .lsr .x .x15 .x11 1,
    .adc .x .x8 .x16 .x16,
    .movz .w .x7 19 0,
    .mul .x .x11 .x7 .x8,
    .adds .x .x12 .x12 .x11,
    .adcs .x .x13 .x13 .x9,
    .adcs .x .x14 .x14 .x3,
    .adc .x .x15 .x15 .x17,
    .stp .x12 .x13 .x0 o,
    .stp .x14 .x15 .x0 (o + 16)]


/-- `sqr_4`: the square of the field element at `a`, below `2·p`, into `o`
(which may be `a`). -/
def sqr4 (o a : Nat) : List Instr :=
  [.ldp .x2 .x3 .x0 a,
    .mul .x .x9 .x2 .x3,
    .umulh .x10 .x2 .x3,
    .ldp .x4 .x5 .x0 (a + 16),
    .mul .x .x11 .x2 .x5,
    .umulh .x12 .x2 .x5,
    .mul .x .x7 .x2 .x4,
    .umulh .x6 .x2 .x4,
    .adds .x .x10 .x10 .x7,
    .adcs .x .x11 .x11 .x6,
    .mul .x .x7 .x3 .x4,
    .umulh .x6 .x3 .x4,
    .adc .x .x6 .x6 .x17,
    .adds .x .x11 .x11 .x7,
    .mul .x .x13 .x4 .x5,
    .umulh .x14 .x4 .x5,
    .adcs .x .x12 .x12 .x6,
    .mul .x .x7 .x3 .x5,
    .umulh .x6 .x3 .x5,
    .adc .x .x6 .x6 .x17,
    .adds .x .x12 .x12 .x7,
    .adcs .x .x13 .x13 .x6,
    .adc .x .x14 .x14 .x17,
    .adds .x .x9 .x9 .x9,
    .adcs .x .x10 .x10 .x10,
    .adcs .x .x11 .x11 .x11,
    .adcs .x .x12 .x12 .x12,
    .adcs .x .x13 .x13 .x13,
    .adcs .x .x14 .x14 .x14,
    .adc .x .x6 .x17 .x17,
    .umulh .x7 .x2 .x2,
    .mul .x .x8 .x2 .x2,
    .adds .x .x9 .x9 .x7,
    .mul .x .x7 .x3 .x3,
    .adcs .x .x10 .x10 .x7,
    .umulh .x7 .x3 .x3,
    .adcs .x .x11 .x11 .x7,
    .mul .x .x7 .x4 .x4,
    .adcs .x .x12 .x12 .x7,
    .umulh .x7 .x4 .x4,
    .adcs .x .x13 .x13 .x7,
    .mul .x .x7 .x5 .x5,
    .adcs .x .x14 .x14 .x7,
    .umulh .x7 .x5 .x5,
    .adc .x .x6 .x6 .x7,
    .movz .w .x3 38 0,
    .mul .x .x7 .x3 .x12,
    .umulh .x4 .x3 .x12,
    .adds .x .x8 .x8 .x7,
    .mul .x .x7 .x3 .x13,
    .umulh .x13 .x3 .x13,
    .adcs .x .x9 .x9 .x7,
    .mul .x .x7 .x3 .x14,
    .umulh .x14 .x3 .x14,
    .adcs .x .x10 .x10 .x7,
    .mul .x .x7 .x3 .x6,
    .umulh .x6 .x3 .x6,
    .adcs .x .x11 .x11 .x7,
    .adc .x .x12 .x17 .x17,
    .adds .x .x11 .x11 .x14,
    .adc .x .x12 .x12 .x6,
    .adds .x .x7 .x11 .x11,
    .lsr .x .x11 .x7 1,
    .adc .x .x2 .x12 .x12,
    .movz .w .x3 19 0,
    .mul .x .x7 .x3 .x2,
    .adds .x .x8 .x8 .x7,
    .adcs .x .x9 .x9 .x4,
    .adcs .x .x10 .x10 .x13,
    .adc .x .x11 .x11 .x17,
    .stp .x8 .x9 .x0 o,
    .stp .x10 .x11 .x0 (o + 16)]


/-- `add_twice4`: the sum of the field elements at `a` and `b`, modulo
`2·p = 2²⁵⁶ − 38`, into `o`: one carry folded back as 38. In four words, and
correct modulo p, if the sum is below `2²⁵⁷ − 38`, as when one of them is
below `2·p`. -/
def addTwice4 (o a b : Nat) : List Instr :=
  [.ldp .x3 .x4 .x0 a,
    .ldp .x7 .x8 .x0 b,
    .adds .x .x3 .x3 .x7,
    .adcs .x .x4 .x4 .x8,
    .ldp .x5 .x6 .x0 (a + 16),
    .ldp .x7 .x8 .x0 (b + 16),
    .adcs .x .x5 .x5 .x7,
    .adcs .x .x6 .x6 .x8,
    .movz .w .x9 38 0,
    .cselc .x .x9 .x9 .x17 .hs,
    .adds .x .x3 .x3 .x9,
    .adcs .x .x4 .x4 .x17,
    .adcs .x .x5 .x5 .x17,
    .adc .x .x6 .x6 .x17,
    .stp .x3 .x4 .x0 o,
    .stp .x5 .x6 .x0 (o + 16)]


/-- `sub_twice4`: the difference of the field elements at `a` and `b`,
modulo `2·p`, into `o`: one borrow folded back as 38. -/
def subTwice4 (o a b : Nat) : List Instr :=
  [.ldp .x5 .x6 .x0 a,
    .ldp .x4 .x3 .x0 b,
    .subs .x .x5 .x5 .x4,
    .sbcs .x .x6 .x6 .x3,
    .ldp .x7 .x8 .x0 (a + 16),
    .ldp .x4 .x3 .x0 (b + 16),
    .sbcs .x .x7 .x7 .x4,
    .sbcs .x .x8 .x8 .x3,
    .movz .w .x4 38 0,
    .cselc .x .x3 .x4 .x17 .lo,
    .subs .x .x5 .x5 .x3,
    .sbcs .x .x6 .x6 .x17,
    .sbcs .x .x7 .x7 .x17,
    .sbc .x .x8 .x8 .x17,
    .stp .x5 .x6 .x0 o,
    .stp .x7 .x8 .x0 (o + 16)]


/-- `cmadd_4`: `c · a + b` for the 64-bit `c` in x1, below `2·p`, into `o`.
Correct if `19 (c · a + b) < 2³¹⁶`. -/
def cmadd4 (o a b : Nat) : List Instr :=
  [.ldp .x7 .x8 .x0 a,
    .ldp .x9 .x10 .x0 (a + 16),
    .mul .x .x3 .x1 .x7,
    .mul .x .x4 .x1 .x8,
    .mul .x .x5 .x1 .x9,
    .mul .x .x6 .x1 .x10,
    .umulh .x7 .x1 .x7,
    .umulh .x8 .x1 .x8,
    .umulh .x9 .x1 .x9,
    .umulh .x10 .x1 .x10,
    .adds .x .x4 .x4 .x7,
    .adcs .x .x5 .x5 .x8,
    .adcs .x .x6 .x6 .x9,
    .adc .x .x10 .x10 .x17,
    .ldp .x7 .x8 .x0 b,
    .adds .x .x3 .x3 .x7,
    .adcs .x .x4 .x4 .x8,
    .ldp .x7 .x8 .x0 (b + 16),
    .adcs .x .x5 .x5 .x7,
    .adcs .x .x6 .x6 .x8,
    .adc .x .x10 .x10 .x17,
    .adds .x .x7 .x6 .x6,
    .lsr .x .x6 .x7 1,
    .adc .x .x8 .x10 .x10,
    .movz .w .x9 19 0,
    .mul .x .x7 .x8 .x9,
    .adds .x .x3 .x3 .x7,
    .adcs .x .x4 .x4 .x17,
    .adcs .x .x5 .x5 .x17,
    .adc .x .x6 .x6 .x17,
    .stp .x3 .x4 .x0 o,
    .stp .x5 .x6 .x0 (o + 16)]


/-- `mux_4`: the field element at `a` if the flags say `ne`, else the one at
`b`, into `o`: four `csel`s, with no branch. -/
def mux4 (o a b : Nat) : List Instr :=
  [.ldp .x4 .x5 .x0 a,
    .ldp .x6 .x7 .x0 b,
    .cselc .x .x4 .x4 .x6 .ne,
    .cselc .x .x5 .x5 .x7 .ne,
    .stp .x4 .x5 .x0 o,
    .ldp .x4 .x5 .x0 (a + 16),
    .ldp .x6 .x7 .x0 (b + 16),
    .cselc .x .x4 .x4 .x6 .ne,
    .cselc .x .x5 .x5 .x7 .ne,
    .stp .x4 .x5 .x0 (o + 16)]

end VG.Impl.X25519.AArch64.Alt
