module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTStep
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTStep
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The search's loop is constant time (ARMv7)

Both runs go on or stop together, to the same next point (`ct_step`),
which consumes more of the tape: the loop rule's measure is the tape left.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.RsaKeyGen.Arm.Search

/-- A finished search of a run whose trace is `T`. -/
def DoneCT (p : SearchPublic) (T : List Nat) (_q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchDone p o (searchResult o) s

def ZeroCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  LiveCT p T q s ∧ isa.eval .eq s = some (decide (q.2.1 = 0))

theorem zero_ready (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (.block [.cmp .r9 (.imm 0)]) s (ZeroCT p T q) := by
  obtain ⟨o, hT, hl, hf⟩ := h
  have := hl.input.remaining_le
  have := hl.remaining_le
  exact WP.mono (cmp0_ok hl.r9 (by omega)) fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨o, hT, hl.keep k hm, hf⟩, he⟩

theorem iteration_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.r9] (fun q s₁ s₂ h₁ h₂ r hr => live_pins p T q s₁ s₂ h₁ h₂ r (by
    obtain rfl := List.mem_singleton.mp hr; simp)) (by taint_decide) (zero_ready p T)) ?_
  refine RelCT.seq (two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (exhausted_ct (live_pins45 fun q s h => h.1.1)) ((candidateStep_ct c p T).mono
      (fun s₁ s₂ ⟨q, h₁, h₂, sp⟩ => ⟨q, ⟨h₁.1.1, ?_⟩, ⟨h₂.1.1, ?_⟩, sp⟩) fun _ _ h => h)) (quiet_ct (by taint_decide))
  · have := h₁.1.2; rw [h₁.2] at this; exact of_decide_eq_false (Option.some.inj this.symm)
  · have := h₂.1.2; rw [h₂.2] at this; exact of_decide_eq_false (Option.some.inj this.symm)

/-- What an iteration leaves, at the point `q`, in public terms. -/
def CTStep (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  if pubCont p T q then isa.eval .eq t = some true ∧ LiveCT p T (nextPt p T q) t
  else isa.eval .eq t = some false ∧ DoneCT p T q t

theorem ct_step (c : Cand) (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (iteration c.call) s (CTStep p T q) := by
  obtain ⟨o, hT, hl, hf⟩ := h
  refine WP.mono (iteration_ok c hl hf) fun t ht => ?_
  unfold IterPost at ht
  unfold CTStep
  have hc := cont_iff hl.input hT hf
  by_cases e : Cont p o q.1 q.2.1
  · rw [ite_eq_left e] at ht
    rw [ite_eq_left (hc.mp e)]
    obtain ⟨he, ht', hf'⟩ := ht
    have hk := e.1
    have eu := used_eq hl.input hT hf hk
    have es := status_eq hT hf hk
    have el := leak_of hT hf hk
    refine ⟨he, o, hT, ?_, ?_⟩
    · unfold nextPt; unfold nextK at ht'; rw [← eu, ← es]; exact ht'
    · unfold nextPt; unfold nextK at hf'; rw [hf', ← eu, ← es, el]
  · rw [ite_eq_right e] at ht
    rw [ite_eq_right (fun h => e (hc.mpr h))]
    exact ⟨ht.1, o, hT, ht.2⟩

/-- Pairs of loop states at the same point, the tape left `n`. -/
def LoopPair (p : SearchPublic) (T : List Nat) (n : Nat) (s t : State) : Prop :=
  ∃ q : Pt, n = p.randLen - q.1 ∧ LiveCT p T q s ∧ LiveCT p T q t ∧ s.sp = t.sp

theorem iteration_pair (c : Cand) (p : SearchPublic) (T : List Nat) (n : Nat) :
    RelCT isa (LoopPair p T n) (iteration c.call) fun s t =>
      isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → Two (DoneCT p T) s t) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair p T m s t) := by
  have wp (q : Pt) (s : State) (h : n = p.randLen - q.1 ∧ LiveCT p T q s) :
      WP isa (iteration c.call) s fun t => n = p.randLen - q.1 ∧ CTStep p T q t :=
    WP.mono (ct_step c p T q s h.2) fun _ r => ⟨h.1, r⟩
  have ct := two_post ((iteration_ct c p T).mono
    (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.2, ht.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, m, hs, ht, sp⟩ => ⟨q, ⟨m, hs⟩, ⟨m, ht⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨m, hs⟩, ⟨_, ht⟩, sp⟩
  unfold CTStep at hs ht
  by_cases e : pubCont p T q
  · rw [ite_eq_left e] at hs ht
    refine ⟨hs.1.trans ht.1.symm, fun h => (by rw [hs.1] at h; cases h), fun _ => ?_⟩
    obtain ⟨o, -, hl, -⟩ := hs.2
    have hb := hl.used_le
    refine ⟨p.randLen - (nextPt p T q).1, ?_, nextPt p T q, rfl, hs.2, ht.2, sp⟩
    have := e.2.2.2
    unfold nextPt at hb ⊢
    omega
  · rw [ite_eq_right e] at hs ht
    refine ⟨hs.1.trans ht.1.symm, fun _ => ⟨q, hs.2, ht.2, sp⟩, fun h => (by rw [hs.1] at h; cases h)⟩

theorem loop_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (.loop (iteration c.call) .eq) (Two (DoneCT p T)) := by
  intro s t ts tt u v ⟨q, hs, ht, sp⟩ es et
  exact RelCT.loop (LoopPair p T) (iteration_pair c p T) (p.randLen - q.1) s t ts tt u v
    ⟨q, rfl, hs, ht, sp⟩ es et

end VG.Proof.RsaKeyGen.Arm.Search
