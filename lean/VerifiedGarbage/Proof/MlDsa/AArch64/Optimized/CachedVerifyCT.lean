module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect

/-! ## From `CachedVerifyRel.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
variable {p : Params}

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

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
  x7 : s₁.gpr .x7 = s₂.gpr .x7

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify

end

/-! ## From `CachedVerifyHash.lean` -/

/-! ## From `CachedVerifyCT.lean` -/

