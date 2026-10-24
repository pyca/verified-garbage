module
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT

import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Writes
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Writes
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Outputs
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # Public positions in the key search, and its exits and rejections (PPC64LE)

Two runs agree on the public descriptor, the octets consumed, the budgets
left and the statuses of the attempts still to come, which the search from
there gives for each run's own tape. The exits and rejections use only
public addresses.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def KeyAny (p : KeyPublic) (s : State) : Prop :=
  ∃ original used keys scalars, KeyLive p original used keys scalars s

structure KeyPoint where
  inputs : KeyPublic
  used : Nat
  keys : Nat
  scalars : Nat
  statuses : List Nat

def KeyCTL (q : KeyPoint) (s : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses

theorem KeyCTL.any {q : KeyPoint} {s : State} (h : KeyCTL q s) : KeyAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, _, h⟩

theorem key_any_pins : Pins KeyAny [.r31] := by
  intro p s t ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

theorem key_ctl_pins : Pins KeyCTL [.r31] :=
  fun _ _ _ h₁ h₂ => key_any_pins _ _ _ h₁.any h₂.any

theorem key_no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at the outputs -/

/-- Before a zeroing's loop: its pointer and count. -/
def KeyZeroCT (j : Nat) (p : KeyPublic) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .r3 = (if j = 5 then p.xp else p.yp) ∧ s.gpr .r4 = BitVec.ofNat 64 p.len

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .r3 j, ldf .r4 2, .li .r5 0]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hk
  rcases hj with rfl | rfl <;>
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => (t.gpr .r3 = (if _ = 5 then p.xp else p.yp) ∧
    t.gpr .r4 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, keys, scalars, h.keep k hm⟩, hr⟩
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    prun [ldf, h.r31, hp, hk, a.ld 40 (by decide), a.ld 16 (by decide)]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    prun [ldf, h.r31, hp, hk, a.ld 48 (by decide), a.ld 16 (by decide)]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyAny) (zeroOut j) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold zeroOut <;>
  · refine RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide))
      (zero_header _ (by decide))) ?_
    exact two_taint [.r3, .r4] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (zeroOut 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) h.input.x_mem
    h.input.x_ne_ctl) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal 3)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide)) terminal_ready)
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .r10 2, .li .r11 0, stf .r10 3, stf .r11 14]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_post (two_taint [.r31] key_any_pins (by taint_decide)) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.r31] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
