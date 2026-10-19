module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # Constant time of a wrapped-seed hash contribution -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

structure PHashPublic where
  plan : HashPlan
  ws : List Region

/-- Only words used as addresses or counters belong to the public frame state. -/
def HashPlan.withWords (p : HashPlan) (W : Nat → BitVec 64)
    (hw : ∀ i < 5, W i = p.W i) : HashPlan :=
  { p with W := W
           seed_slot := (hw 1 (by decide)).trans p.seed_slot
           wrapped_slot := (hw 3 (by decide)).trans p.wrapped_slot
           output_slot := (hw 4 (by decide)).trans p.output_slot
           offset_slot := (hw 2 (by decide)).trans p.offset_slot }

def PHashBefore (n : Nat) (H : Spec.Mgf1.Hash) (k : Nat) (p : PHashPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i < 5, W i = p.plan.W i,
    HashState (p.plan.withWords W hw) H k s ∧ FrV n p.plan.F p.ws s

def PSeedReady (n : Nat) (H : Spec.Mgf1.Hash) (k j : Nat) (p : PHashPublic) (s : State) : Prop :=
  PHashBefore n H k p s ∧ s.gpr .rsi = p.plan.seedPtr ∧ s.gpr .rdi = p.plan.wrapped ∧
    s.gpr .rax = BitVec.ofNat 64 (p.plan.offset + j)

def PHashPublic.label (p : PHashPublic) : LQ :=
  ⟨p.plan.F, p.plan.S, p.ws, p.plan.wrapped, p.plan.len⟩

theorem seedInputArgs_ready {n k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j < 2 ^ 31) (h : PHashBefore n H k p s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedInputArgs j)) s (PSeedReady n H k j p) := by
  obtain ⟨W, hw, h⟩ := h
  let q := p.plan.withWords W hw
  obtain ⟨V, R⟩ := h.1.rep
  refine WP.mono (seedInputArgs_ok hj h.1.layout R q.seed_slot q.wrapped_slot
    q.offset_slot) fun t ⟨hsi, hdi, hax, hm, hk⟩ => ?_
  refine ⟨⟨W, hw, ?_, h.2.congr (hk.gpr (by decide)) hk.2.2⟩, hsi, hdi, hax⟩
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
  obtain ⟨_, _, hs, _⟩ := hs
  obtain ⟨_, _, ht, _⟩ := ht
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem wrappedSeed_label {n k j : Nat} {H : Spec.Mgf1.Hash} {p : PHashPublic} {s : State}
    (hj : j ≤ p.plan.count) (h : PSeedReady n H k j p s) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAdd p.plan.len) s (LW n p.label) := by
  obtain ⟨⟨W, hw, hs, hfr⟩, hsi, hdi, hax⟩ := h
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
      exact p.plan.seed_wrap _ (he ▸ a) b)
  rw [hlen] at hc
  refine WP.mono hc fun t ⟨_, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hs.rep
  have Rt := rep_of_external_write R p.plan.wrapped_sep hf
  have Lt := lay_of_rep hs.layout R Rt rfl (hk.gpr (by decide)) hk.2.2
  exact ⟨hfr.congr (hk.gpr (by decide)) hk.2.2, Lt, V, W, Rt,
    hs.hashArgs.congr hk.2.1 hk.2.2 rfl rfl⟩

end VG.Proof.Dsa.X86_64.Generation
