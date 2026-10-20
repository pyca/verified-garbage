module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Streaming hash contributions for the public p-candidate search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

def ContributionBefore (n : Nat) (H : Spec.Mgf1.Hash) (k len count : Nat)
    (p : PHashPublic) (s : State) : Prop :=
  PHashBefore n H k p s ∧ p.plan.len = len ∧ p.plan.count = count

def ContributionReady (n : Nat) (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (p : PHashPublic) (s : State) : Prop :=
  PSeedReady n H k j p s ∧ p.plan.len = len ∧ p.plan.count = count

theorem contributionArgs_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count j : Nat) (hj : j < 2 ^ 31) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (.block (Impl.Dsa.X86_64.Generation.seedInputArgs j))
      (Two (ContributionReady n H k len count j)) := by
  refine two_post ((seedInputArgs_ct n H k j hj).mono
    (fun _ _ => two_mono fun _ _ h => h.1) (fun _ _ _ => True.intro)) ?_
  intro p s h
  exact WP.mono (seedInputArgs_ready hj h.1) fun _ ht => ⟨ht, h.2⟩

theorem contributionWrap_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (hlen : len = 20 ∨ len = 32) (hj : j ≤ count) :
    RelCT isa (Two (ContributionReady n H k len count j))
      (Impl.Dsa.X86_64.Generation.seedAdd len) (Two fun (p : PHashPublic) s => LW n p.label s) := by
  have pins : Pins (ContributionReady n H k len count j) [.rdi, .rsi] := by
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
    · exact hs.1.2.1.trans ht.1.2.1.symm
  have ct : RelCT isa (Two (ContributionReady n H k len count j))
      (Impl.Dsa.X86_64.Generation.seedAdd len) (fun _ _ => True) := by
    rcases hlen with rfl | rfl
    · exact seedAdd20_ct pins
    · exact seedAdd32_ct pins
  refine two_post ct ?_
  intro p s h
  have hw := wrappedSeed_label (show j ≤ p.plan.count by rw [h.2.2]; exact hj) h.1
  rw [h.2.1] at hw
  exact hw

theorem pSeedHash_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (k len count j : Nat)
    (hlen : len = 20 ∨ len = 32) (hj : j ≤ count) (hj' : j < 2 ^ 31) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pSeedHash G len j) (fun _ _ => True) := by
  refine RelCT.seq (contributionArgs_ct n H k len count j hj')
    (RelCT.seq (contributionWrap_ct n H k len count j hlen hj) ?_)
  exact two_map PHashPublic.label (fun _ _ h => h) (hashLabel_ct hG n hn (Or.inl rfl))

end VG.Proof.Dsa.X86_64.Generation
