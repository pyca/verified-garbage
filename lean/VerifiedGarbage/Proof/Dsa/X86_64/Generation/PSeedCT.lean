module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT

/-! # Constant time of a wrapped-seed hash contribution -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

structure PHashPublic where
  plan : HashPlan
  ws : List Region

def PHashBefore (n : Nat) (H : Spec.Mgf1.Hash) (k : Nat) (p : PHashPublic) (s : State) : Prop :=
  HashState p.plan H k s ∧ FrV n p.plan.F p.ws s

def PSeedReady (n : Nat) (H : Spec.Mgf1.Hash) (k j : Nat) (p : PHashPublic) (s : State) : Prop :=
  PHashBefore n H k p s ∧ s.gpr .rsi = p.plan.seedPtr ∧ s.gpr .rdi = p.plan.wrapped ∧
    s.gpr .rax = BitVec.ofNat 64 (p.plan.offset + j)

def PHashPublic.label (p : PHashPublic) : LQ :=
  ⟨p.plan.F, p.plan.S, p.ws, p.plan.wrapped, p.plan.len⟩

theorem seedInputArgs_ready {n k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j < 2 ^ 31) (h : PHashBefore n H k p s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedInputArgs j)) s (PSeedReady n H k j p) := by
  obtain ⟨V, R⟩ := h.1.rep
  refine WP.mono (seedInputArgs_ok hj h.1.layout R p.plan.seed_slot p.plan.wrapped_slot
    p.plan.offset_slot) fun t ⟨hsi, hdi, hax, hm, hk⟩ => ?_
  refine ⟨⟨?_, h.2.congr (hk.gpr (by decide)) hk.2.2⟩, hsi, hdi, hax⟩
  refine ⟨h.1.layout.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]),
    ⟨V, hm ▸ R⟩, h.1.hashArgs.congr hk.2.1 hk.2.2 rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hk.2.1, hk.2.2]; exact h.1.seedRead i hi
  · intro i hi; rw [hk.2.2]; exact h.1.wrappedWrite i hi
  · intro i hi; rw [hk.2.2]; exact h.1.outputWrite i hi
  · rw [hm]; exact h.1.seed
  · intro i hi; rw [hm]; exact h.1.hashes i hi

theorem seedInputArgs_ct (n : Nat) (H : Spec.Mgf1.Hash) (k j : Nat) (hj : j < 2 ^ 31) :
    RelCT isa (Two (PHashBefore n H k)) (.block (Impl.Dsa.X86_64.Generation.seedInputArgs j))
      (Two (PSeedReady n H k j)) := by
  refine two_post (two_taint [.rsp] ?_ (hc := .block []) (by rfl))
    (fun _ _ h => seedInputArgs_ready hj h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.1.layout.rsp.trans ht.1.layout.rsp.symm

theorem wrappedSeed_label {n k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j ≤ p.plan.count) (h : PSeedReady n H k j p s) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAdd p.plan.len) s (LW n p.label) := by
  have plen := p.plan.size.2.1
  have carry := p.plan.carry
  have hlen := p.plan.seed_len
  have hb : ∀ i < p.plan.seed.length, s.mem (off p.plan.seedPtr i) = p.plan.seed.getD i 0 := by
    intro i hi
    rw [← h.1.1.seed]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hlen ▸ hi]
  have hc := seedAdd_ok p.plan.seed (by omega) (show p.plan.offset + j < 2 ^ 32 by omega)
    h.2.1 h.2.2.1 h.2.2.2
    (fun i hi => h.1.1.seedRead i (hlen ▸ hi)) (fun i hi => h.1.1.wrappedWrite i (hlen ▸ hi)) hb (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      exact p.plan.seed_wrap _ (he ▸ a) b)
  rw [hlen] at hc
  refine WP.mono hc fun t ⟨_, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := h.1.1.rep
  have Rt := rep_of_external_write R p.plan.wrapped_sep hf
  have Lt := lay_of_rep h.1.1.layout R Rt rfl (hk.gpr (by decide)) hk.2.2
  exact ⟨h.1.2.congr (hk.gpr (by decide)) hk.2.2, Lt, V, p.plan.W, Rt,
    h.1.1.hashArgs.congr hk.2.1 hk.2.2 rfl rfl⟩

end VG.Proof.Dsa.X86_64.Generation
