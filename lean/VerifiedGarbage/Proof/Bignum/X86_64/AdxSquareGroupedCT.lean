module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareGrouped
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareGrouped
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! All addresses and loop decisions depend only on the two bases and word count. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def PublicInputs (values : Reg → BitVec 64) (s : State) : Prop :=
  ∀ r ∈ [.r8,.r9,.r10], s.gpr r = values r

theorem diagonal_ct : RelCT isa (Two PublicInputs) AdxSquareGrouped.diagonal (fun _ _ => True) := by
  apply two_taint [.r8,.r9,.r10]
  · intro values s t hs ht r hr
    exact (hs r hr).trans (ht r hr).symm
  · taint_decide

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
