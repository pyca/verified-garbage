module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Stored-power arithmetic and public key checks have fixed instruction traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

theorem precomputedSetup_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (precomputedSetup n)
      (.seq (workspaceTaint false) (.block []) (oneHint false)) = some (zerosTaint false) := by
  unfold precomputedSetup
  exact exponent_check_seq taint (setupInverse_taint false (slot n 0) inverseOffset) (by rfl)
    (one_check false n (slot n 4))

theorem precomputedPower_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (precomputedPower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  exact VG.RelCT.seq (checkedProgramChange (precomputedSetup_check n) (by rfl))
    (checkedProgramChange (PublicContext.exponentiate_check n) (by rfl))

theorem precomputedAcceptAndPower_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (PrecomputedFn.acceptAndPower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have Save : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx])
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl
  exact VG.RelCT.seq (inputCompare_relCT n) (VG.RelCT.seq Save (precomputedPower_relCT n))

theorem precomputedChecks_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (precomputedChecks n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (precomputedChecks n) (precomputedChecks 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (precomputedChecks 1)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
