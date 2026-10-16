module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Safety
public import VerifiedGarbage.Spec.Ffdh.Contract
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Verify FFDH key-generation attempts for every Montgomery backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem generateCode_verified (v : RoundImpl) : Verified target (generateCode v)
    (Spec.Ffdh.generateKeyContract abi) := by
  apply gk_verified v.mont (CrtExpL.w4 v.mont) (R2Impl.words v.mont) _ (generateCode_mx v)
  exact two_map id (fun _ _ h => h.1)
    (crtExpLoop_ct v.mont CrtSel.sse CrtSel.sse_ct (by taint_decide))

end VG.Proof.Ffdh.X86_64.GenerateKey
