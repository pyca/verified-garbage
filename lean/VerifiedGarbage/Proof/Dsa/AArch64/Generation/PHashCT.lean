module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedCT

/-! # Streaming hash contributions for the public p-candidate search -/

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
