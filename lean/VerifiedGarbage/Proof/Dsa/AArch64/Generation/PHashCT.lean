module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAddCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
/-! # Streaming hash contributions for the public p-candidate search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PSeedCT.lean`, which only this module imported.
section

/-! # Constant time of a wrapped-seed hash contribution -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

structure PHashPublic where
  plan : HashPlan

/-- Only words used as addresses or counters belong to the public frame state. -/
def HashPlan.withWords (p : HashPlan) (W : Nat → BitVec 64)
    (hw : ∀ i < 5, W i = p.W i) : HashPlan :=
  { p with W := W
           seed_slot := (hw 1 (by decide)).trans p.seed_slot
           wrapped_slot := (hw 3 (by decide)).trans p.wrapped_slot
           output_slot := (hw 4 (by decide)).trans p.output_slot
           offset_slot := (hw 2 (by decide)).trans p.offset_slot }

def PHashBefore (H : Spec.Mgf1.Hash) (k : Nat) (p : PHashPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i < 5, W i = p.plan.W i,
    HashState (p.plan.withWords W hw) H k s

def PSeedReady (H : Spec.Mgf1.Hash) (k j : Nat) (p : PHashPublic) (s : State) : Prop :=
  PHashBefore H k p s ∧ s.gpr .x1 = p.plan.seedPtr ∧ s.gpr .x2 = p.plan.wrapped ∧
    s.gpr .x0 = BitVec.ofNat 64 (p.plan.offset + j)

theorem seedInputArgs_ready {k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j < 4096) (h : PHashBefore H k p s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedInputArgs j)) s (PSeedReady H k j p) := by
  obtain ⟨W, hw, h⟩ := h
  let q := p.plan.withWords W hw
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (seedInputArgs_ok hj h.layout R q.seed_slot q.wrapped_slot
    q.offset_slot) fun t ⟨hsi, hdi, hax, hm, hk⟩ => ?_
  refine ⟨⟨W, hw, ?_⟩, hsi, hdi, hax⟩
  refine ⟨h.layout.congr hk.sp hk.wr (by rw [hm]),
    ⟨V, hm ▸ R⟩, h.hashArgs.congr hk.rd hk.wr rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hk.rd, hk.wr]; exact h.seedRead i hi
  · intro i hi; rw [hk.wr]; exact h.wrappedWrite i hi
  · intro i hi; rw [hk.wr]; exact h.outputWrite i hi
  · rw [hm]; exact h.seed
  · intro i hi; rw [hm]; exact h.hashes i hi

theorem seedInputArgs_ct (H : Spec.Mgf1.Hash) (k j : Nat) (hj : j < 4096) :
    RelCT isa (Two (PHashBefore H k)) (.block (Impl.Dsa.AArch64.Generation.seedInputArgs j))
      (Two (PSeedReady H k j)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (hc := .block []) (by rfl))
    (fun _ _ h => seedInputArgs_ready hj h)

theorem wrappedSeed_label {k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j ≤ p.plan.count) (h : PSeedReady H k j p s) :
    WP isa (Impl.Dsa.AArch64.Generation.seedAdd p.plan.len) s (fun t => ∃ V W, Lay t p.plan.F p.plan.S ∧ Rep t.mem p.plan.F p.plan.S V W ∧
      LabAt t p.plan.F p.plan.S W p.plan.wrapped p.plan.len) := by
  obtain ⟨⟨W, hw, hs⟩, hsi, hdi, hax⟩ := h
  have plen := p.plan.size.2.1
  have carry := p.plan.carry
  have hlen := p.plan.seed_len
  have hb : ∀ i < p.plan.seed.length, s.mem (off p.plan.seedPtr i) = p.plan.seed.getD i 0 := by
    intro i hi
    have he : Spec.Rsa.bytesAt s.mem p.plan.seedPtr p.plan.len = p.plan.seed := hs.seed
    rw [← he]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hlen ▸ hi]
  have hc := seedAdd_ok p.plan.seed (by omega) (show p.plan.offset + j < 2 ^ 32 by omega)
    hsi hdi hax
    (fun i hi => hs.seedRead i (hlen ▸ hi)) (fun i hi => hs.wrappedWrite i (hlen ▸ hi)) hb (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      apply p.plan.seed_wrap _ a
      simpa only [← he] using b)
  rw [hlen] at hc
  refine WP.mono hc fun t ⟨_, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hs.rep
  have Rt := rep_of_external_write R p.plan.wrapped_sep hf
  have Lt := lay_of_rep hs.layout R Rt rfl hk.sp hk.wr
  exact ⟨V, W, Lt, Rt, hs.hashArgs.congr hk.rd hk.wr rfl rfl⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

def ContributionBefore (H : Spec.Mgf1.Hash) (k len count : Nat)
    (p : PHashPublic) (s : State) : Prop :=
  PHashBefore H k p s ∧ p.plan.len = len ∧ p.plan.count = count

def ContributionReady (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (p : PHashPublic) (s : State) : Prop :=
  PSeedReady H k j p s ∧ p.plan.len = len ∧ p.plan.count = count

theorem contributionArgs_ct (H : Spec.Mgf1.Hash) (k len count j : Nat) (hj : j < 4096) :
    RelCT isa (Two (ContributionBefore H k len count))
      (.block (Impl.Dsa.AArch64.Generation.seedInputArgs j))
      (Two (ContributionReady H k len count j)) := by
  refine two_post ((seedInputArgs_ct H k j hj).mono
    (fun _ _ => two_mono fun _ _ h => h.1) (fun _ _ _ => True.intro)) ?_
  intro p s h
  exact WP.mono (seedInputArgs_ready hj h.1) fun _ ht => ⟨ht, h.2⟩

theorem contributionWrap_ct (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (hlen : len = 20 ∨ len = 32) (hj : j ≤ count) :
    RelCT isa (Two (ContributionReady H k len count j))
      (Impl.Dsa.AArch64.Generation.seedAdd len) (Two fun (p : PHashPublic) s => ∃ V W, Lay s p.plan.F p.plan.S ∧ Rep s.mem p.plan.F p.plan.S V W ∧ LabAt s p.plan.F p.plan.S W p.plan.wrapped len) := by
  have pins : Pins (ContributionReady H k len count j) [.x1, .x2] := by
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.2.1.trans ht.1.2.1.symm
    · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
  have ct : RelCT isa (Two (ContributionReady H k len count j))
      (Impl.Dsa.AArch64.Generation.seedAdd len) (fun _ _ => True) := by
    rcases hlen with rfl | rfl
    · exact seedAdd20_ct pins
    · exact seedAdd32_ct pins
  refine two_post ct ?_
  intro p s h
  have hw := wrappedSeed_label (show j ≤ p.plan.count by rw [h.2.2]; exact hj) h.1
  rw [h.2.1] at hw
  exact hw

theorem pSeedHash_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (hlen : len = 20 ∨ len = 32) (hj : j ≤ count) (hj' : j < 4096) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pSeedHash G len j) (fun _ _ => True) := by
  refine RelCT.seq (contributionArgs_ct H k len count j hj')
    (RelCT.seq (contributionWrap_ct H k len count j hlen hj) ?_)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨p, hs, ht, _⟩ := hp
  obtain ⟨Vs, Ws, Ls, Rs, As⟩ := hs
  obtain ⟨Vt, Wt, Lt, Rt, At⟩ := ht
  exact hashLabel_tr hG (by rcases hlen with h | h <;> omega) (Or.inl rfl)
    (X := fun W s => LabAt s p.plan.F p.plan.S W p.plan.wrapped len) (fun _ _ h => h)
    s t tr1 tr2 u v ⟨⟨Vs, Ws, Ls, Rs, As⟩, ⟨Vt, Wt, Lt, Rt, At⟩⟩ e1 e2

end VG.Proof.Dsa.AArch64.Generation
