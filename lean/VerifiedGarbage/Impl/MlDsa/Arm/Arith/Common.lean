module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# ML-DSA on 32-bit ARM: arithmetic modulo `q`

Pieces of code that the ML-DSA functions share, for `q = 8380417 < 2²³`. The
baseline has only the 32-bit multiplications `mul` and `mla` (the long
multiplications are left out, see `TCB/Arm/Isa.lean`), so a product of two
reduced values, which has up to 46 bits, is never formed: its low 32 bits
are (`mul`), and a multiple of `q` close to it is subtracted, modulo `2³²`,
which leaves the difference itself where that is less than `2³²`. `-q` is
in a register `N`, so that a subtraction of a multiple of `q` is an `mla`.

* `red d t N`: `d ← d - ⌊d / 2²³⌋ · q`, for any 32-bit `d`: as
  `2²³ ≡ 2¹³ - 1`, the result is congruent to `d` and at most
  `2²³ - 1 + 511 · 8191 < 1.5 · 2²³`;
* `quot zp z`: `zp ← ⌊(z + ⌊z / 2¹⁰⌋) / 2⁷⌋`, for `z < q`: `⌊2¹⁶ z / q⌋` or
  one less, as `2²³ / q = 1 + 2⁻¹⁰ + …`;
* `mulq acc b z zp t N`: `acc ← b · z - ⌊⌊b / 2⁸⌋ · zp / 2⁸⌋ · q`, for
  `b < 1.5 · 2²³`, `z < q` and its `zp`: `⌊b / 2⁸⌋ · zp < 2³²`, and its
  quotient by `2⁸` is at most `b · z / q` and close enough to it that the
  result, which is congruent to `b · z`, is less than `2³² - q`
  (`Proof/MlDsa/Arith/Mul32.lean`);
* `mulz acc b t`: `acc ← b · z` modulo `q` (less than `1.5 · 2²³`), for any
  32-bit `b`, which it reduces first (`red`), and `z` and its `zp` in `r6`
  and `r7`, and `-q` in `r4`: `red`, `mulq`, `red`;
* `csub d t Q`: `d ← d mod q` for `d < 2q`, with `q` in `Q`: `d - q`, plus
  `q` if that is negative (as a two's complement number), with `t` as the
  mask: `(d >> 31) · q` is `q` or 0.

A function that uses more registers than `r0`–`r3` and `r12` saves them in
frames on the stack, one per register (`saving`), and restores each with
the pop of its frame.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- `r ← q = 0x7FE001`. -/
def loadQ (r : Reg) : List Instr := [.movw r 0xE001, .movt r 0x7F]

/-- `r ← -q = 2³² - q = 0xFF801FFF`. -/
def loadNQ (r : Reg) : List Instr := [.movw r 0x1FFF, .movt r 0xFF80]

/-- `d ← d - ⌊d / 2²³⌋ · q`, with `-q` in `N` and `t` a temporary. -/
def red (d t N : Reg) : List Instr := [.mov t (.shifted d .lsr 23), .mla d t N d]

/-- `zp ← ⌊(z + ⌊z / 2¹⁰⌋) / 2⁷⌋`. -/
def quot (zp z : Reg) : List Instr := [.dp .add zp z (.shifted z .lsr 10), .mov zp (.shifted zp .lsr 7)]

/-- `acc ← b · z - ⌊⌊b / 2⁸⌋ · zp / 2⁸⌋ · q`, with `-q` in `N` and `t` a
temporary. -/
def mulq (acc b z zp t N : Reg) : List Instr :=
  [.mov t (.shifted b .lsr 8), .mul t t zp, .mov t (.shifted t .lsr 8), .mul acc b z, .mla acc t N acc]

/-- `acc ← b · z` modulo `q` (less than `1.5 · 2²³`), for `z` and its `zp`
in `r6` and `r7` and `-q` in `r4`, with `t` a temporary; `b` is reduced. -/
def mulz (acc b t : Reg) : List Instr := red b t .r4 ++ mulq acc b .r6 .r7 t .r4 ++ red acc t .r4

/-- `d ← d - q`, plus `q` if that is negative: `d mod q` for `d < 2q`, with
`q` in `Q` and `t` a temporary. -/
def csub (d t Q : Reg) : List Instr := [.dp .sub d d (.reg Q), .mov t (.shifted d .lsr 31), .mla d t Q d]

/-- `body`, with the registers `rs` saved in a frame each around it. -/
def saving : List Reg → Prog isa → Prog isa
  | [], body => body
  | r :: rs, body => .frame (.push [r]) (saving rs body) (.pop r 4)

end VG.Impl.MlDsa.Arm.Arith
