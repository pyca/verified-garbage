module

public import VerifiedGarbage.Impl.Bignum.X86.WideProduct
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Schoolbook multiplication branches and addresses depend only on public widths -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem wideProduct_relCT (N out a b mult : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (wideProduct N out a b mult)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (wideProduct N out a b mult) (wideProduct 1 0 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (wideProduct 1 0 0 0 0)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
