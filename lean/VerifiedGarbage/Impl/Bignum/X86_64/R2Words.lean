import VerifiedGarbage.Impl.Bignum.X86_64

/-!
# `R² mod m` by word steps (x86-64)

For a modulus `m` of `w` words whose top bit is set (`2^(64 w - 1) ≤ m`)
and `w` a multiple of 4, `R² mod m` (`R = 2^(64 w)`) from `R mod m = R - m`
by `w / 4` steps `x := x 2^64 mod m`, which give `2^(16 w) R mod m`, then
two Montgomery squarings, which give `2^(64 w) R mod m`: where the doublings
of `vg_rsa_public`'s computation add one bit at a time, each step adds a
word, as a step of long division (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D):

* the quotient `q = ⌊x 2^64 / m⌋` is estimated as
  `q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` from the top words `u₂`, `u₁` of
  `x` and `d` of `m`, by restoring division, a bit at a time (`quot`), which
  for `d ≥ 2^63` gives `q ≤ q̂ ≤ q + 2`;
* `t = x 2^64 - q̂ m` into the accumulator, over `w + 1` words in two's
  complement (`mulSub`);
* `m` added to `t` while it is negative, twice, by a mask (`addBack`);
* `t` back into `x`.

Every branch and address depends only on `w`; the arithmetic on `m`'s words
(which are public) is branch-free. Other moduli take `vg_rsa_public`'s
computation (`old`); `choice` takes this one when it can.
-/

namespace VG.Impl.Bignum.X86_64.R2Words

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-! ## A step -/

/-- The bases of `x` (`aR2`), `m` and the accumulator, in `rbx`, `r10` and
`r8`, and `w` in `r12`. -/
def bases : List Instr :=
  [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r8 (.mem (hdr (sArr aAcc))),
    .mov .r12 (.mem (hdr sW))]

/-- The divisor `d = m[w - 1]` into `rsi`, the dividend's top word
`u₂ = x[w - 1]` into `rdx` and the next `u₁ = x[w - 2]` into `rax`; `r9` all
ones if `u₂ = d` (as `x < m` has `u₂ ≤ d`, if `d - u₂ < 1`), and then `rdx`
zero; the quotient `rcx := 0` and the count `r13 := 64`. -/
def divHead : List Instr :=
  [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.mem (ix .rbx .r12 (-8))), .mov .rax (.mem (ix .rbx .r12 (-16))),
    .mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)), .alu .and .rdx (.reg .r11),
    .mov32 .rcx (.imm 0), .mov32 .r13 (.imm 64)]

/-- A bit of restoring division by `d` (`rsi`) of the remainder `r < d`
(`rdx`) and the next bit of `u₁` (the top of `rax`): `r := 2 r + bit`, with
its carry; subtract `d` if the carry is set or `r ≥ d` (into `r15`, a mask),
by `cmov`; the quotient `rcx := 2 rcx + 1` if so, `2 rcx` otherwise; and the
count `r13` down. -/
def divBit : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .adc .rdx (.reg .rdx), .alu .sbb .r11 (.reg .r11),
    .mov .r14 (.reg .rdx), .alu .sub .r14 (.reg .rsi), .alu .sbb .r15 (.reg .r15),
    .alu .xor .r15 (.imm (-1)), .alu .or .r15 (.reg .r11), .alu .test .r15 (.reg .r15),
    .cmov .ne .rdx (.reg .r14), .alu .add .rcx (.reg .rcx), .alu .sub .rcx (.reg .r15),
    .alu .sub .r13 (.imm 1)]

/-- `q̂` into `rcx`: 64 bits of the division, all ones if `u₂ = d`. -/
def quot : Prog isa :=
  .seq (.block divHead) (.seq (.loop (.block divBit) .ne) (.block [.alu .or .rcx (.reg .r9)]))

/-- Word 0 of `t = x 2^64 - q̂ m`: `0 - lo(q̂ m₀)`, its borrow into `rbp`
(a mask) and `hi(q̂ m₀)` into `r9`. -/
def subHead : List Instr :=
  [.mov .rax (.mem (at0 .r10)), .mul .rcx, .mov .r9 (.reg .rdx), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .store (at0 .r8) .rdx, cfToRbp]

/-- Word `i = r14` of `t`: `x[i - 1] - lo(q̂ mᵢ + r9) - borrow`, and
`r9 := hi(q̂ mᵢ + r9)`. -/
def subBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9), .alu .adc .rdx (.imm 0),
    .mov .r9 (.reg .rdx), .mov .rdx (.mem (ix .rbx .r14 (-8))), cfFromRbp, .alu .sbb .rdx (.reg .rax), cfToRbp,
    .store (ix .r8 .r14) .rdx]

/-- Word `w` of `t`: `x[w - 1] - r9 - borrow`. -/
def subTop : List Instr :=
  [.mov .rdx (.mem (ix .rbx .r12 (-8))), cfFromRbp, .alu .sbb .rdx (.reg .r9), .store (ix .r8 .r12) .rdx]

/-- `t := x 2^64 - q̂ m` over `w + 1` words, modulo `2^(64 (w + 1))`. -/
def mulSub : Prog isa := .seq (.block subHead) (.seq (wordLoop 1 subBody) (.block subTop))

/-- The mask of `t`'s sign (the top bit of its word `w`) into `r11`, and no
carry in `rbp`. -/
def addHead : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), .alu .add .rax (.reg .rax), .alu .sbb .r11 (.reg .r11), .mov32 .rbp (.imm 0)]

/-- Word `i = r14` of `t := t + (m & mask)`. -/
def addBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r11), cfFromRbp, .alu .adc .rax (.mem (ix .r8 .r14)),
    cfToRbp, .store (ix .r8 .r14) .rax]

/-- Word `w` of `t` plus the carry. -/
def addTop : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax]

/-- `t := t + m` if `t` is negative, modulo `2^(64 (w + 1))`. -/
def addBack : Prog isa := .seq (.block addHead) (.seq (wordLoop 0 addBody) (.block addTop))

/-- `w` words of the accumulator (`r8`) into `x` (`rbx`), as `copyWords` copies
them from `rsi`. -/
def copyBack : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r8)]) (wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax])

/-- `x := x 2^64 mod m`. -/
def step : Prog isa := seqs [.block bases, quot, mulSub, addBack, addBack, copyBack]

/-- `step` `rcx` times (a public count, at least 1), counted in `sCnt`. -/
def steps : Prog isa :=
  .seq (.block [.store (hdr sCnt) .rcx])
    (.loop (.seq step (.block [.mov .rcx (.mem (hdr sCnt)), .alu .sub .rcx (.imm 1), .store (hdr sCnt) .rcx])) .ne)

/-! ## `R² mod m` -/

/-- Word `i = r14` of `x := 0 - m`, the borrow in `rbp`. -/
def negBody : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp, .store (ix .rbx .r14) .rax]

variable (mul : Nat → Nat → Nat → Prog isa)

/-- `x := R - m`, `w / 4` steps, and two squarings. -/
def fast : Prog isa := seqs [
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 negBody,
  .block [.mov .rcx (.mem (hdr sW)), .shift .shr .rcx 2],
  steps,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2]

/-- `vg_rsa_public`'s computation of `R² mod m`: `2^(b - 1)` for the bit
length `b` of `m`, doubled `64 - j + w` times (for the top bit `j` of its top
word), and squared six times. -/
def old : List (Prog isa) := [
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2]

/-- ZF set iff the top bit of `m`'s top word is set and `w` (`r12`) is a
multiple of 4, for `m` at `r10`. -/
def fastTest : List Instr :=
  [.mov .rax (.mem (ix .r10 .r12 (-8))), .shift .shr .rax 63, .alu .xor .rax (.imm 1), .mov .rcx (.reg .r12),
    .alu .and .rcx (.imm 3), .alu .or .rax (.reg .rcx)]

/-- `R² mod m` by `fast` when it applies, by `old` otherwise. -/
def choice : Prog isa := .seq (.block fastTest) (.ite .e (fast mul) (seqs (old mul)))

end VG.Impl.Bignum.X86_64.R2Words
