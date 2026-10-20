module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Input acceptance and exponentiation have no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem acceptAndPower_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (PublicFn.acceptAndPower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have Save : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx])
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl
  have Power : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (VG.Impl.Bignum.X86.PublicContext.publicPower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
    checkedProgramChange (PublicContext.publicPower_check n) rfl
  exact VG.RelCT.seq (inputCompare_relCT n) (VG.RelCT.seq Save Power)

end VG.Proof.Bignum.X86
