module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # Big-endian counter increments on PPC64LE: of 128 bits, and of GCM's last 32 -/

@[expose] public section

namespace VG.Impl.Modes.PPC64LE

open VG.PPC64LE

/-- Increment the 128-bit big-endian counter at `base + off`, using only
`r8` and `r9`: the second doubleword plus 1, then the first plus the carry,
`1 - nz` with `nz = ((0 - lo) | lo) >> 63` (`1` iff the new second
doubleword `lo` is nonzero), with no branch. -/
def incAt (base : Reg) (off : Nat) : List Instr :=
  [.li .r9 (off + 8), .loadRev .d .r8 base .r9, .addi .r8 .r8 1, .storeRev .d .r8 base .r9,
   .li .r9 0, .sub .r9 .r9 .r8, .logic .or .r9 .r9 .r8, .lsr .d .r9 .r9 63,
   .li .r8 off, .loadRev .d .r8 base .r8, .addi .r8 .r8 1, .sub .r8 .r8 .r9,
   .li .r9 off, .storeRev .d .r8 base .r9]

/-- Increment the 32-bit big-endian word at `base + off` modulo 2³² (GCM's
`inc₃₂` on a counter block's last word), using only `r8` and `r9`. -/
def inc32At (base : Reg) (off : Nat) : List Instr :=
  [.li .r9 off, .loadRev .w .r8 base .r9, .addi .r8 .r8 1, .storeRev .w .r8 base .r9]

end VG.Impl.Modes.PPC64LE
