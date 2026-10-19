module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate

/-! Validate the generated domain using the existing native DSA checker. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def validateArgs (pLen qLen : Nat) : List Instr :=
  [.ldrSp .x0 40, mov .x4 .x0, movi .x3 VG.Impl.Dsa.Generation.Layout.packed,
   .add .x .x0 .x0 .x3, movi .x3 VG.Impl.Dsa.Generation.Layout.domainCheck,
   .add .x .x4 .x4 .x3, movi .x2 pLen, movi .x3 qLen]

def validate (mul : Nat → Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.seq (.block (validateArgs pLen qLen)) (Generate.checkParameters mul))
    (.ite (.zero .x .x0) (.block (stackStatus 3)) (.block (stackStatus 1)))

end VG.Impl.Dsa.AArch64.Generation
