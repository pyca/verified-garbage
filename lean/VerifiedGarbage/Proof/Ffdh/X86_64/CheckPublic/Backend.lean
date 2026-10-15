module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Verify FFDH public-key validation for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem publicCode_verified (v : RoundImpl) : Verified target (publicCode v)
    (Spec.Ffdh.checkPublicContract abi) := by
  apply cp_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (publicCode_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

end VG.Proof.Ffdh.X86_64.CheckPublic
