module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Early verification failure returns zero -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyFailure_ok (s : State) :
    WP isa (.block [movi .x0 0]) s fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem) ?_ (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨ht, hmem⟩, hk⟩ => ⟨ht, hmem, hk⟩
  brun

end VG.Proof.Dsa.AArch64
