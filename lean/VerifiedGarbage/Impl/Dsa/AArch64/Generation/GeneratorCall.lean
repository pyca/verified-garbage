module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Calling the generator stage from the persistent generation frame

The stage is a function of its own (`vg_dsa_generator_{bits}`), called with
the scratch base (frame word 5) as its working space and the h tape (words
11 and 13). Its result, 1 for parameters and 0 to go on, is stored as the
generation's status 1 or 3 in word 19. -/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- The stage's arguments: `ws`, its words, and the h tape. -/
def generatorCallArgs (pLen : Nat) : List Instr :=
  [.ldrSp .x0 40, movi .x1 (VG.Impl.Dsa.Generation.Layout.usedBytes pLen / 8),
   .ldrSp .x2 88, .ldrSp .x3 104]

/-- The result, a `u32` in `w0`, stored as the status 3 - 2 * r. -/
def generatorCallStatus : List Instr :=
  [.addImm .w .x0 .x0 0, movi .x3 3, .sub .x .x3 .x3 .x0, .sub .x .x3 .x3 .x0, .strSp .x3 152]

/-- The stage for a p of `pLen` bytes, called as `gen pLen`. -/
def generatorCall (gen : Nat → Prog isa) (pLen : Nat) : Prog isa :=
  .seq (.block (generatorCallArgs pLen)) (.seq (gen pLen) (.block generatorCallStatus))

end VG.Impl.Dsa.AArch64.Generation
