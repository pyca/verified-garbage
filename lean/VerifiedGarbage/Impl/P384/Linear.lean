module

public import VerifiedGarbage.Impl.P384.Ops

/-!
# P-384's small linear combinations on AArch64

`lin o a b c d` is `[o] = c [a] - d [b] mod p`, with one reduction, as
s2n-bignum's `cmsub_p384` (`arm/p384/p384_montjdouble_alt.S`) computes it:
`p - [b]` (from the modulus's slot), times `d` (`rowInit`), plus `c [a]`
(`row`), is `V < (c + d) p`, which one quotient estimate `q`, the top word
plus one, reduces: `V - q p` is in `[-p, p)`, so `p` is added back where it
is negative. The words of `q (2^384 - p)` and of `p` under a mask are
computed, as the allocator follows only loads, `movz` and register
operations. The doubling's `12 a - 9 b`, `4 a - b` and `3 a - 8 b` are
instances.
-/

@[expose] public section

namespace VG.Impl.P384.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64

/-- `p - [b]`, then `d (p - [b])`. -/
def qRegs : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13]

/-- The sum `V`, then (its low words) the result. -/
def rRegs : List Reg := [.x1, .x4, .x5, .x6, .x14, .x15, .x16]

/-- The low words of `rRegs`. -/
def lowRegs : List Reg := [.x1, .x4, .x5, .x6, .x14, .x15]

/-- `rRegs = d (p - [b])`. -/
def scaleB (b d : Nat) : List Instr :=
  zero7 :: loads qRegs Ops.M.mo ++ chain (.subs .x) (.sbcs .x) qRegs b ++
    ([.movz .x .x17 (BitVec.ofNat 16 d) 0, .movz .x .x16 0 0] : List Instr) ++
    rowInit .x0 .x17 rRegs qRegs

/-- `rRegs += c [a]`. -/
def addA (a c : Nat) : List Instr :=
  .movz .x .x17 (BitVec.ofNat 16 c) 0 :: row .x0 .x17 rRegs (mWords a 0 6)

/-- `q = top + 1`, and `lowRegs += q (2^384 - p) = q (2^128 + 2^96 - 2^32 + 1)`,
with the carry out: whether `V ≥ q p`. -/
def fold : List Instr :=
  ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32, .subs .x .x2 .x16 .x3,
    .sbc .x .x3 .x3 .x7] : List Instr) ++
  Mont.AArch64.P384Mul.addsIn true lowRegs [.x2, .x3, .x16, .x7, .x7, .x7]

/-- `lowRegs += p` where the fold did not carry, modulo `2^384`: `p`'s words
from the mask `m` (`x17`), `m >> 32`, `m ^ (m >> 32)`, `m << 1` and `m`. -/
def correct : List Instr :=
  ([.sbc .x .x17 .x7 .x7, .lsr .x .x2 .x17 32, .logic .eor .x .x3 .x17 .x2,
    .lsl .x .x16 .x17 1] : List Instr) ++
  Mont.AArch64.P384Mul.addsIn true lowRegs [.x2, .x3, .x16, .x17, .x17, .x17]

/-- `[o] = c [a] - d [b] mod p` (`o` may be `a` or `b`). -/
def lin (o a b c d : Nat) : List Instr :=
  scaleB b d ++ addA a c ++ fold ++ correct ++ stores lowRegs o

end VG.Impl.P384.Linear
