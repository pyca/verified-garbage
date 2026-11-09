module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Calling the generator stage from the persistent generation frame

The stage is a function of its own (`vg_dsa_generator_{bits}`), called with
the scratch base (frame word 5) as its working space and the h tape (words
11 and 13); its result (`Proof.Dsa.GeneratorStage.result`) is returned in
`x0`. -/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- The stage's arguments: `ws`, its words, and the h tape. -/
def generatorCallArgs (pLen : Nat) : List Instr :=
  [.ldrSp .x0 40, movi .x1 (VG.Impl.Dsa.Generation.Layout.usedBytes pLen / 8),
   .ldrSp .x2 88, .ldrSp .x3 104]

end VG.Impl.Dsa.AArch64.Generation
