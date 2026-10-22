module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTAttempt
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTAttempt
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify

/-! # Two runs after an attempt (x86)

After attempts with the same status, `classify` branches alike in both
runs, and each of its blocks is checked by the taint analysis from `esi`
and `esp` (`classify_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A run's state with the public descriptor `p`. -/
def Any (p : KPub) (s : State) : Prop := ∃ o ds f, ofState o = p ∧ St o ds f s

theorem any_pins {α : Type} {Φ : α → State → Prop} (g : α → KPub) (h : ∀ a s, Φ a s → Any (g a) s) :
    Pins Φ [.esi, .esp] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨o₁, _, _, e₁, S₁⟩ := h a s₁ h₁
  obtain ⟨o₂, _, _, e₂, S₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [S₁.esi, S₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [S₁.esp, S₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- After an attempt with the status `k.2`. -/
def ClsAt (k : Ap) (u : State) : Prop :=
  ∃ o, ofState o = k.1.1 ∧ St o liveDs (liveF k.1.1 (o.gpr .esi) k.1.2.1 k.1.2.2.1 k.1.2.2.2) u ∧
    u.gpr .eax = BitVec.ofNat 32 k.2 ∧ (1 ≤ k.2 ∧ k.2 ≤ 3) ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen

/-- The status in `edx` compared with `j`. -/
def CmpAt (j : Nat) (k : Ap) (t : State) : Prop :=
  Any k.1.1 t ∧ (1 ≤ k.2 ∧ k.2 ≤ 3) ∧ t.gpr .edx = BitVec.ofNat 32 k.2 ∧ isa.eval .e t = some (decide (k.2 = j))

theorem cmpAt_pins (j : Nat) : Pins (CmpAt j) [.esi, .esp] := any_pins (fun k => k.1.1) fun _ _ h => h.1

theorem cmp_ok {k : Ap} {t : State} {i : Nat} (h : CmpAt i k t) (j : Nat) (hj : j ≤ 3) :
    WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 j))]) t (CmpAt j k) := by
  obtain ⟨⟨o, ds, f, e, S⟩, hk, he, _⟩ := h
  refine wp_cmpi fun t' F _ z => WP.block_nil ⟨⟨o, ds, f, e, S.fupd F⟩, hk, by rw [F.gpr]; exact he, ?_⟩
  exact cmp_status hk.2 hj he z

theorem ne_of {j : Nat} {k : Ap} {s : State} (h : CmpAt j k s) (hf : isa.eval .e s = some false) : k.2 ≠ j := by
  rw [h.2.2.2] at hf
  simpa using hf

/-- A branch never taken: the status is 1, 2 or 3. -/
theorem never {k : Ap} {s : State} (h : CmpAt 3 k s ∧ isa.eval .e s = some false) (h1 : k.2 ≠ 1) (h2 : k.2 ≠ 2) :
    False := by
  obtain ⟨⟨_, hk, _, he⟩, hf⟩ := h
  rw [he] at hf
  simp only [Option.some.injEq, decide_eq_false_iff_not] at hf
  omega

theorem classify_ct : RelCT isa (Two ClsAt) classify fun _ _ => True := by
  unfold classify
  refine RelCT.seq (two_piece (Ψ := CmpAt 1) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun k s ⟨o, e, S, _⟩ => ⟨o, _, _, e, S⟩) (by taint_decide)
    fun k u ⟨o, e, S, he, hk, hr⟩ => ?_) ?_
  · obtain ⟨⟨p, used, keys, scalars⟩, st⟩ := k
    dsimp only at e S he hk hr ⊢
    subst e
    exact advance_ok S hr fun t S' hed _ => wp_cmpi fun t' F _ z => WP.block_nil
      ⟨⟨o, _, _, rfl, S'.fupd F⟩, hk, by rw [F.gpr, hed, he], cmp_status hk.2 (by decide) (hed.trans he) z⟩
  refine two_ite (fun k _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := fun k t => CmpAt 2 k t ∧ k.2 ≠ 1) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun _ _ h => h.1.1) (by taint_decide)
    fun k t h => WP.mono (cmp_ok h.1 2 (by decide)) fun _ h' => ⟨h', ne_of h.1 h.2⟩) ?_
  refine two_ite (fun k _ _ h₁ h₂ => h₁.1.2.2.2.trans h₂.1.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := fun k t => CmpAt 3 k t ∧ k.2 ≠ 1 ∧ k.2 ≠ 2) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)
    fun k t h => WP.mono (cmp_ok h.1.1 3 (by decide)) fun _ h' => ⟨h', h.1.2, ne_of h.1.1 h.2⟩) ?_
  refine two_ite (fun k _ _ h₁ h₂ => h₁.1.2.2.2.trans h₂.1.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)) ?_
  exact fun _ _ _ _ _ _ ⟨k, h₁, _⟩ => (never ⟨h₁.1.1, h₁.2⟩ h₁.1.2.1 h₁.1.2.2).elim

end VG.Proof.Ffdh.X86.KeySearch
