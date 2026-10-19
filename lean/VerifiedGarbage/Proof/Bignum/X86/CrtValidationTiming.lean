module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCoreTiming

/-! # Acceptance checks and saved masks never affect private CRT control flow -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

theorem mergeAcceptance_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block mergeAcceptance)
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl

theorem validate_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (validate n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have Save : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.store (VG.Impl.Mont.X86.sc acceptanceOffset) .edx])
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl
  exact VG.RelCT.seq (checkFactorProduct_relCT _ _ _ _ _ _)
    (VG.RelCT.seq Save (VG.RelCT.seq (lessThan_relCT false _ _ _)
      (VG.RelCT.seq mergeAcceptance_relCT (VG.RelCT.seq (lessThan_relCT false _ _ _) mergeAcceptance_relCT))))

theorem maskResult_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (maskResult n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (checkedBlockInvariant rfl rfl) (maskOutput_relCT n)

end VG.Proof.Bignum.X86.Crt
