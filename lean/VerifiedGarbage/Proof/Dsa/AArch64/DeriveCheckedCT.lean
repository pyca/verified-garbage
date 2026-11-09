module

public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveMainCT
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveBodyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveMainCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveBodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-! # Constant time of AArch64 DSA key derivation for a checked domain -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem deriveCheckedBodySched_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (fun _ _ => True) := by
  have h4 := publicPrefix_ct M deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M) (RelCT.seq deriveCopy_ct ?_))
  exact (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => h.1) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem deriveCheckedComputed_ok (M : Mont) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveCheckedBody_ok (L := c.layout.withInverses pi qi) M hr (c.pre.scratch.congr hk.wr)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength
    c.input.xLength rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveCheckedSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveCheckedBodySched_ct M).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveCheckedComputed_ok M h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveCheckedMain_ct (M : Mont) :
    RelCT isa (Two DeriveStart) (Generate.deriveChecked M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveCheckedSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
