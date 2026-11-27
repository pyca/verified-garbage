module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem

/-!
# ML-KEM on AArch64: the comparison and the choice of the key in `decaps`

The end of `Decaps_internal` (FIPS 203 Algorithm 18), which the decapsulation of
`Kem16P.lean` runs: `c = c'` without branching, by the OR of the bytes of `c ⊕ c'`
(`deCmp`), a mask of ones if it is 0, and `K'` or `K̄` into `key` through the
mask (`deSel`). Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64 KEM

/-- One word of `c ⊕ c'` ORed into `x10`. -/
def deCmpBody : List Instr :=
  [.ldr .x .x9 .x0 0, .ldr .x .x11 .x1 0, .logic .eor .x .x9 .x9 .x11, .logic .orr .x .x10 .x10 .x9,
    .addImm .x .x0 .x0 8, .addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1]

/-- Eight bytes of `K'` or `K̄` into `key`, through the mask in `x10`. -/
def deSelWord (k : Nat) : List Instr :=
  [.ldr .x .x12 .x28 (KP + 8 * k), .ldr .x .x13 .x28 (JB + 8 * k), .logic .eor .x .x12 .x12 .x13,
    .logic .and .x .x12 .x12 .x10, .logic .eor .x .x12 .x12 .x13, .str .x .x12 .x27 (8 * k)]

/-- `K'` or `K̄` into `key`. -/
def deSel : List Instr := (List.range 4).flatMap deSelWord

namespace KemLay

variable (L : KemLay)

/-- The OR of the words of `c ⊕ c'` into `x10`, then a mask in `x10`: all
ones if it is 0 (`c = c'`), and 0 otherwise (`(x ∨ -x) >> 63` is 1 exactly
when `x ≠ 0`). -/
def deCmp : Prog isa :=
  .seq (.block (ptrTo .x0 .x26 0 ++ ptrTo .x1 .x28 (CB L) ++
      ([.movz .x .x2 (BitVec.ofNat 16 (L.ctLen / 8)) 0, .movz .x .x10 0 0] : List Instr))) <|
  .seq (.loop (.block deCmpBody) (.nonzero .x .x2))
    (.block [.movz .x .x11 0 0, .sub .x .x11 .x11 .x10, .logic .orr .x .x10 .x10 .x11, .lsr .x .x10 .x10 63,
      .subImm .x .x10 .x10 1])

end KemLay

end VG.Impl.MlKem.AArch64
