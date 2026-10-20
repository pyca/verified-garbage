module

public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Constant-time ordinary modular products and sums -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem ordinaryMul_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (ordinaryMul n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedProgramChange (τ' := rowTaint false) (hint := .seq (workspaceTaint false) (mulHint false) (mulHint false))
    (exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) (mul_check false _ _ _ _ _ _)) rfl

theorem ordinaryAdd_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (ordinaryAdd n)
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
  checkedProgramChange (hint := addHint true) (add_check true _ _ _ _ _) rfl

end VG.Proof.Dsa.X86
