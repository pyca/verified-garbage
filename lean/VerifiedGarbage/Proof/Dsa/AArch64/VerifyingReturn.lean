module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Algebra.Group.Nat.Defs

/-! # Both verifying branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def VerifyingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.verifyBytes p.pLen p.qLen p.key p.signature p.digest).toNat ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem verifyingRejected_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block [movi .x0 0]) s
      (VerifyingPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hfalse := verifyBytes_invalid_shape (signature := p.signature) (digest := p.digest) hparams
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
  unfold VerifyingPost
  rw [hfalse]
  exact ⟨hret,
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
