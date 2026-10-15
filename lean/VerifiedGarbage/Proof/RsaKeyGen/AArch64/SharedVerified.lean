module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Implies
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTCode
import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # RSA candidate verification with a shared Miller–Rabin kernel -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

theorem sharedCandidate_verified (M : Mont) (R : Kernel) :
    Verified target (VG.Impl.RsaKeyGen.AArch64.Candidate.codeWith M.mm R.run)
      (Spec.RsaKeyGen.candidateContract abi) := by
  exact Verified.of_correct (sharedCode_correct M R)
    (sharedCode_constantTime M R (sharedKMain_ct M R (sharedTail_ct M R))) cand_implies

end VG.Proof.RsaKeyGen.AArch64
