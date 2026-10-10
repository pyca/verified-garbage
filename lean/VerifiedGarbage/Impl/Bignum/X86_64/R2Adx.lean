import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

/-!
# `R² mod m` by word steps with ADX (x86-64)

For a public modulus `m` of `w` words whose top bit is set and `w` a
multiple of 4, as `R2Words.fast`: `R² mod m` (`R = 2^(64 w)`) from
`R mod m = R - m`, but by all `w` steps `x := x 2^64 mod m` and no
Montgomery squarings, each step a single pass over the words:

* the quotient `q̂` is `R2Words.quot`'s, `q ≤ q̂ ≤ q + 2`;
* `t = x 2^64 - q̂ m = x 2^64 + q̂ (R - m) - q̂ R` is computed in place, into
  `x`'s `w + 1` words, with `R - m` (`mc`, computed once, in the
  accumulator) multiplied by `mulx`, its halves added by `adox` and the sum
  added to `x` shifted by a word by `adcx`: two carry chains, four words a
  tile, carried in registers between tiles (`tile`), and `q̂` subtracted from
  the top word;
* `m` added back while `t` is negative (at most twice), by a branch on the
  sign of its top word: the modulus is public, and so is every value here.

Other moduli take `vg_rsa_public`'s computation (`R2Words.old`).
-/

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

/-- The carries out of the flags: `OF` into the high word `r9`, `CF` into the
mask `r14`; and the next tile. -/
def tileTail : List Instr :=
  [.adox .r9 (.reg .rcx), .alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm 4), .alu .cmp .r15 (.reg .r12)]

/-- Four words of `t`, the previous word of `x` in `r8` and the high word in
`r9`, before and after. -/
def tile : List Instr :=
  tileHead ++ word 0 .r8 .r13 .r9 .rax ++ word 1 .r13 .r8 .rax .r9 ++ word 2 .r8 .r13 .r9 .rax ++
    word 3 .r13 .r8 .rax .r9 ++ tileTail

/-- `q̂` into `rdx`, `mc` (the accumulator) into `rsi`, and no carries. -/
def mulHead : List Instr :=
  [.mov .rdx (.reg .rcx), .mov .rsi (.mem (hdr (sArr aAcc))), .mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0),
    .mov32 .r14 (.imm 0), .mov32 .r15 (.imm 0)]

/-- `t[w] = x[w - 1] + hi + CF - q̂`. -/
def mulTop : List Instr :=
  [.alu .xor .rcx (.reg .rcx), .alu .add .r14 (.reg .r14), .adcx .r8 (.reg .r9), .alu .sub .r8 (.reg .rdx),
    .store (ix .rbx .r12) .r8]

/-- `t := x 2^64 + q̂ mc - q̂ R` in place, over `w + 1` words. -/
def mulSub : Prog isa := .seq (.block mulHead) (.seq (.loop (.block tile) .ne) (.block mulTop))

/-- `t := t + m` if `t` is negative: `R2Words.addBack` at `x`. -/
def fix : Prog isa :=
  .seq (.block [.mov .rax (.mem (ix .rbx .r12)), .alu .add .rax (.reg .rax)])
    (.ite .b (.seq (.block [.mov .r8 (.reg .rbx)]) addBack) (.block []))

/-- `x := x 2^64 mod m`. -/
def step : Prog isa := seqs [.block R2Words.bases, .block quot, mulSub, fix, fix]

/-- `step` `rcx` times (a public count, at least 1), counted in `sCnt`. -/
def steps : Prog isa :=
  .seq (.block [.store (hdr sCnt) .rcx])
    (.loop (.seq step (.block [.mov .rcx (.mem (hdr sCnt)), .alu .sub .rcx (.imm 1), .store (hdr sCnt) .rcx])) .ne)

/-! ## `R² mod m` -/

/-- `x := R - m`, `mc := x`, `v`, and `w` steps. -/
def fast : Prog isa := seqs [
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
    .mov .r8 (.mem (hdr (sArr aTmp))), .mov32 .rbp (.imm 0)],
  wordLoop 0 negBody,
  .block [.mov .r8 (.reg .rbx), .mov .rbx (.mem (hdr (sArr aAcc)))],
  copyBack,
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r8 (.mem (hdr (sArr aTmp)))],
  recip,
  .block [.mov .rcx (.mem (hdr sW))],
  steps]

/-- `R² mod m` by `fast` when it applies, by `R2Words.old` otherwise. -/
def choice (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block fastTest) (.ite .e fast (seqs (old mul)))

end VG.Impl.Bignum.X86_64.R2Adx
