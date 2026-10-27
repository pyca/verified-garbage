module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeInput
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeInput
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Trial division reads public workspace metadata in the generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64

structure PrimeCallPublic where
  draw : DrawPublic
  arena : Addr
  wr : List Region
  /-- The arena is the generation's last writable region, or the second of
  a called test's (`vg_dsa_probable_prime_*`). -/
  layout : PrimeHeaderLayout arena wr ∨ CalleeHeaderLayout arena wr
  base : draw.prime.B = off arena 28672
  width : draw.prime.w ≤ 48
  tab : slot draw.prime.w aTab + 2048 ≤ draw.prime.Z
  large : 8161 < draw.prime.N
  policy : 1024 < Spec.Dsa.bitLength draw.prime.N ↔ 16 < draw.prime.w

def PrimeCallBefore (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  (∃ mi, PrimeInput p.draw.prime mi p.draw.used s) ∧ s.wr = p.wr ∧
    p.draw.used ≤ p.draw.prime.rand.length ∧ p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem primeTrial_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeCallBefore len drawBytes))
    (seqs trial) (fun _ _ => True) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  rcases p.layout with hl | hl
  · refine primeHeader_ct (Φ := fun p s => PrimeCallBefore len drawBytes p s ∧ PrimeHeaderLayout p.arena p.wr)
      PrimeCallPublic.arena PrimeCallPublic.wr gS
      (fun p => gvs p.draw.prime.B p.draw.prime.w) [] (by decide) (fun _ => gvs_fst _ _) ?_
      (pins_nil _) (by taint_decide) _ _ _ _ _ _ ⟨p, ⟨h₁, hl⟩, h₂, hl⟩ e₁ e₂
    intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact ⟨h.2, by rw [← p.base]; exact good_hp hs.good h.1.2.1⟩
  · refine calleeHeader_ct (Φ := fun p s => PrimeCallBefore len drawBytes p s ∧ CalleeHeaderLayout p.arena p.wr)
      PrimeCallPublic.arena PrimeCallPublic.wr gS
      (fun p => gvs p.draw.prime.B p.draw.prime.w) [] (by decide) (fun _ => gvs_fst _ _) ?_
      (pins_nil _) (by taint_decide) _ _ _ _ _ _ ⟨p, ⟨h₁, hl⟩, h₂, hl⟩ e₁ e₂
    intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact ⟨h.2, by rw [← p.base]; exact good_hp hs.good h.1.2.1⟩

def PrimeCallTested (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  PrimeCallBefore len drawBytes p s ∧
    s.zf = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength p.draw.prime.N) p.draw.prime.N)

theorem primeTrial_tested {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) :
    WP isa (seqs trial) s (PrimeCallTested len drawBytes p) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (primeTrial_ok hs p.width p.tab p.large p.policy) fun _ ⟨hz, ht, _, hk⟩ =>
    ⟨⟨⟨mi, ht⟩, hk.2.2.trans h.2.1, h.2.2⟩, hz⟩

end VG.Proof.Dsa.X86_64.Generation
