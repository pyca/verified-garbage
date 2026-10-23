module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateBody
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Functional correctness of the complete separate DSA public-key validator -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (Prevalidated.validate M.mm) s0 (ValidatingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (validatingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x3 == (0#64)) = some true
      simp only [hs.branch, ha, Bool.not_false]
    · have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
      change ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params at hp
      have hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = false := by
        simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
          p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [hp, decide_false, Bool.false_and]
      refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
        (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
      exact ⟨by rw [hv]; exact hret, by rw [hmem]; exact hs.frame,
        (hs.keep.trans hk).mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (s.gpr .x3 == (0#64)) = some false
      simp only [hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (validatingInitialize_ok h hs ha) fun t ht => ?_)
      exact validatingBody_ok M h ht ha

end VG.Proof.Dsa.AArch64
