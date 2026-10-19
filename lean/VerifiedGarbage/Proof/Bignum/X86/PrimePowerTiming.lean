module

public import VerifiedGarbage.Impl.Bignum.X86.PrimePower
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Factor validity and secret exponent bits never select addresses or branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem sanitizeModulus_relCT (n modulus temporary : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (sanitizeModulus n modulus temporary) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (sanitizeModulus n modulus temporary) (sanitizeModulus 1 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (sanitizeModulus 1 0 0)) rfl rfl rfl
  rfl

theorem preparePrime_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (preparePrime n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  refine VG.RelCT.seq (sanitizeModulus_relCT n _ _) ?_
  exact checkedProgramChange (contextSetup_check n) (by rfl)

theorem primePower_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (primePower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  refine VG.RelCT.seq (preparePrime_relCT n) ?_
  exact checkedProgramChange (exponentiate_check n (2 * n) (by omega)) (by rfl)

end VG.Proof.Bignum.X86
