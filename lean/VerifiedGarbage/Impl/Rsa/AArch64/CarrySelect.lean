module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! Multiword selection with a loop-invariant carry flag. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.CarrySelect
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Select `[x16]` into `[x17]` when `x15` is all ones, over `x14`
words. Subtracting one from the mask sets the carry flag once; the loop
preserves it and uses `csel` without a secret-dependent branch. -/
def code : Prog isa :=
 .seq (.block [movi .x3 1, .subs .x .x3 .x15 .x3])
  (countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .csel .x .x4 .x3 .x4,
   st .x4 .x17, next .x16, next .x17])

end VG.Impl.Rsa.AArch64.CarrySelect
