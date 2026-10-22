module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

/-!
# `R² mod m` by word steps with ADX (x86-64)

For a public modulus `m` of `w` words whose top bit is set and `w` a
multiple of 4, as `R2Words.fast`: `R² mod m` (`R = 2^(64 w)`) from
`R mod m = R - m`, but by all `w` steps `x := x 2^64 mod m` and no
Montgomery squarings, each step a single pass over the words:

* the reciprocal of `m`'s top word that `q̂` uses is found by six Newton
  steps from a guess, then corrected one at a time down and up until it is
  exact (`recipN`), rather than by `R2Words.recip`'s 64 steps of division;
* the quotient `q̂` is `R2Words.quot`'s, `q ≤ q̂ ≤ q + 2`, refined twice by
  `m`'s second word (`refine`), which keeps it at least `q`;
* `t = x 2^64 - q̂ m = x 2^64 + q̂ (R - m) - q̂ R` is computed in place, into
  `x`'s `w + 1` words, with `R - m` (`mc`, computed once, in the
  accumulator) multiplied by `mulx`, its halves added by `adox` and the sum
  added to `x` shifted by a word by `adcx`: two carry chains, four words a
  tile, kept in the flags across a group of tiles (eight for `w` a multiple
  of 32, four for 16, else one) and in registers between groups (`tiles`),
  and `q̂` subtracted from the top word;
* `m` added back while `t` is negative (at most twice), by a branch on the
  sign of its top word: the modulus is public, and so is every value here.

Other moduli take `vg_rsa_public`'s computation (`R2Words.old`).
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.R2Adx

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Words

/-! ## A step -/

/-- Word `k` of a tile (`r15` the tile's first word): `lo + 2^64 hiN = q̂ mc[i]`
(`mulx`, `q̂` in `rdx`, `mc` at `rsi`), `lo += hiP + OF` (`adox`), the next
word of `x` into `next` before `t[i] = prev + lo + CF` (`adcx`) replaces
it. -/
def word (k : Nat) (prev next hiP hiN : Reg) : List Instr :=
  [.mulx hiN .r11 (.mem (ix .rsi .r15 (8 * k))), .adox .r11 (.reg hiP), .mov next (.mem (ix .rbx .r15 (8 * k))),
    .adcx prev (.reg .r11), .store (ix .rbx .r15 (8 * k)) prev]

/-- The carries into the flags: both clear, then `CF` from the mask `r14`. -/
def tileHead : List Instr := [.alu .xor .rcx (.reg .rcx), .alu .add .r14 (.reg .r14)]

/-- Four words of `t`, the words `4 i` to `4 i + 3` from `r15`, the previous
word of `x` in `r8` and the high word in `r9`, before and after. -/
def tileWords (i : Nat) : List Instr :=
  word (4 * i) .r8 .r13 .r9 .rax ++ word (4 * i + 1) .r13 .r8 .rax .r9 ++ word (4 * i + 2) .r8 .r13 .r9 .rax ++
    word (4 * i + 3) .r13 .r8 .rax .r9

/-- `g` tiles, the carries in the flags from one to the next. -/
def groupWords : Nat → List Instr
  | 0 => []
  | g + 1 => groupWords g ++ tileWords g

/-- `g` tiles (`4 g` words, `inc = 4 g`) between the carries' moves into and
out of the flags: the loop's control, which clobbers `CF`, runs once a
group. -/
def group (g : Nat) (inc : BitVec 32) : List Instr :=
  tileHead ++ groupWords g ++
    ([.adox .r9 (.reg .rcx), .alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm inc), .alu .cmp .r15 (.reg .r12)] :
      List Instr)

/-- ZF set iff `w` (`r12`) is a multiple of `k + 1` (a power of two), by `rax`. -/
def wTest (k : BitVec 32) : List Instr := [.mov .rax (.reg .r12), .alu .and .rax (.imm k)]

/-- The tiles over `w` words: in groups of eight if `w` is a multiple of 32
(2048 and 4096 bits), of four if of 16 (3072 bits), else one at a time. -/
def tiles : Prog isa :=
  .seq (.block (wTest 31)) (.ite .e (.loop (.block (group 8 32)) .ne)
    (.seq (.block (wTest 15)) (.ite .e (.loop (.block (group 4 16)) .ne) (.loop (.block (group 1 4)) .ne))))

/-- `q̂` into `rdx`, `mc` (the accumulator) into `rsi`, and no carries. -/
def mulHead : List Instr :=
  [.mov .rdx (.reg .rcx), .mov .rsi (.mem (hdr (sArr aAcc))), .mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0),
    .mov32 .r14 (.imm 0), .mov32 .r15 (.imm 0)]

/-- `t[w] = x[w - 1] + hi + CF - q̂`. -/
def mulTop : List Instr :=
  [.alu .xor .rcx (.reg .rcx), .alu .add .r14 (.reg .r14), .adcx .r8 (.reg .r9), .alu .sub .r8 (.reg .rdx),
    .store (ix .rbx .r12) .r8]

/-- `t := x 2^64 + q̂ mc - q̂ R` in place, over `w + 1` words. -/
def mulSub : Prog isa := .seq (.block mulHead) (.seq tiles (.block mulTop))

/-- `t := t + m` if `t` is negative: `R2Words.addBack` at `x`. -/
def fix : Prog isa :=
  .seq (.block [.mov .rax (.mem (ix .rbx .r12)), .alu .add .rax (.reg .rax)])
    (.ite .b (.seq (.block [.mov .r8 (.reg .rbx)]) addBack) (.block []))

/-- Knuth's test with the second words (TAOCP vol. 2, §4.3.1, Algorithm D,
step D3), for `q̂` in `rcx`: `q̂ := q̂ - 1` if `r̂ = u₂ 2^64 + u₁ - q̂ d < 2^64`
(`r̂` into `r11:r9`, its high word zero) and `q̂ d₁ > r̂ 2^64 + u₀`, for `m`'s
second word `d₁` and `x`'s third `u₀`, by a mask; `q̂` stays at least the
quotient, and is it but rarely after two tests. -/
def refine : List Instr :=
  [.mov .rdx (.reg .rcx), .mulx .rax .r13 (.mem (ix .r10 .r12 (-8))),
    .mov .r9 (.mem (ix .rbx .r12 (-16))), .mov .r11 (.mem (ix .rbx .r12 (-8))),
    .alu .sub .r9 (.reg .r13), .alu .sbb .r11 (.reg .rax),
    .mulx .rax .r13 (.mem (ix .r10 .r12 (-16))), .mov .r14 (.mem (ix .rbx .r12 (-24))),
    .alu .sub .r14 (.reg .r13), .alu .sbb .r9 (.reg .rax), .alu .sbb .r15 (.reg .r15),
    .mov32 .r13 (.imm 0), .alu .test .r11 (.reg .r11), .cmov .ne .r15 (.reg .r13), .alu .add .rcx (.reg .r15)]

/-- `x := x 2^64 mod m`. -/
def step : Prog isa := seqs [.block R2Words.bases, .block quot, .block refine, .block refine, mulSub, fix, fix]

/-- `step` `rcx` times (a public count, at least 1), counted in `sCnt`. -/
def steps : Prog isa :=
  .seq (.block [.store (hdr sCnt) .rcx])
    (.loop (.seq step (.block [.mov .rcx (.mem (hdr sCnt)), .alu .sub .rcx (.imm 1), .store (hdr sCnt) .rcx])) .ne)

/-! ## The reciprocal -/

/-- A Newton step towards `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d` (`rsi`) from
`v` (`rcx`), as `x = 2^64 + v` approximates `2^128 / d` from below: the
high word `e = 2^64 - 1 - (d + ⌊v d / 2^64⌋)` of the error `2^128 - x d`,
and `v := v + e + ⌊v e / 2^64⌋`, which is `x + ⌊x e / 2^64⌋`. Only the
speed of `recipN` depends on how close it comes. -/
def recipStep : List Instr :=
  [.mov .rdx (.reg .rcx), .mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .xor .r14 (.imm (-1)),
    .mov .rdx (.reg .r14), .mulx .r11 .rax (.reg .rcx), .alu .add .r14 (.reg .r11), .alu .add .rcx (.reg .r14)]

/-- `d = m[w - 1]` into `rsi`, the first guess `v = 2^64 - 1 - d` into `rcx`
(`x = 2^65 - 1 - d`, within a quarter of `2^128 / d`), and six Newton
steps. -/
def recipGuess : List Instr :=
  [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rcx (.reg .rsi), .alu .xor .rcx (.imm (-1))] ++
    (List.replicate 6 recipStep).flatten

/-- `v := v - 1` if `(2^64 + v) d ≥ 2^128` (the carry of `d + ⌊v d / 2^64⌋`),
by a mask in `rax`; ZF clear iff it was. -/
def recipDown : List Instr :=
  [.mov .rdx (.reg .rcx), .mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax),
    .alu .add .rcx (.reg .rax), .alu .test .rax (.reg .rax)]

/-- `v := v + 1` if `v + 1 < 2^64` and `(2^64 + v + 1) d < 2^128`, by a mask
in `rax`; ZF clear iff it was. -/
def recipUp : List Instr :=
  [.mov .rdx (.reg .rcx), .alu .add .rdx (.imm 1), .alu .sbb .r11 (.reg .r11), .mulx .r14 .rax (.reg .rsi),
    .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax), .alu .or .rax (.reg .r11), .alu .xor .rax (.imm (-1)),
    .alu .sub .rcx (.reg .rax), .alu .test .rax (.reg .rax)]

/-- `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d = m[w - 1] ≥ 2^63` into the first
word of the temporary (at `r8`), as `R2Words.recip` but by `recipGuess`, then
`recipDown` and `recipUp` while they change it: whatever `recipGuess` gives,
`v` is then the largest with `(2^64 + v) d < 2^128`. The loops branch on
values of the public modulus. -/
def recipN : Prog isa := seqs [.block recipGuess, .loop (.block recipDown) .ne, .loop (.block recipUp) .ne,
  .block [.store (at0 .r8) .rcx]]

/-! ## `R² mod m` -/

/-- `x := R - m`, `mc := x`, `v`, and `w` steps. -/
def fast : Prog isa := seqs [
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
    .mov .r8 (.mem (hdr (sArr aTmp))), .mov32 .rbp (.imm 0)],
  wordLoop 0 negBody,
  .block [.mov .r8 (.reg .rbx), .mov .rbx (.mem (hdr (sArr aAcc)))],
  copyBack,
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r8 (.mem (hdr (sArr aTmp)))],
  recipN,
  .block [.mov .rcx (.mem (hdr sW))],
  steps]

/-- `R² mod m` by `fast` when it applies, by `R2Words.old` otherwise. -/
def choice (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block fastTest) (.ite .e fast (seqs (old mul)))

end VG.Impl.Bignum.X86_64.R2Adx
