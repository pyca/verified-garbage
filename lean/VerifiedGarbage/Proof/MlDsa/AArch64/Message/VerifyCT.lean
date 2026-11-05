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
message, the context string and the signature (`verifyI`), `μ` at `X + 840`
(`VMuOk`), what a layout says of `sig` and `scratch` (`VFacts`), and the
public data of the arguments in `x0`–`x6` (`VPub`).
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

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What a layout of `verify_message_cached` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.pkLen
  xSig : L.XS.Disjoint ⟨L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 64
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.rd
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .x0) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat ++
      bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat ++ bytesAt s₁.mem (s₁.gpr .x5) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .x0) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat ++
      bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat ++ bytesAt s₂.mem (s₂.gpr .x5) p.sigLen)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6

end

end VG.Proof.MlDsa.AArch64.Message
