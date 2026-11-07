module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on AArch64, `verify_message_cached`: what two runs agree on

Untrusted: everything here is checked by Lean. What the proofs that the
cached message verifier runs in constant time
(`Proof/MlDsa/AArch64/Optimized/CachedVerifyCT.lean`,
`RootedCachedVerifyCT.lean`) share: the public inputs of two runs, `pk`, the
message, the context string and the signature (`verifyI`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

end

end VG.Proof.MlDsa.AArch64.Message
