module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTClassify
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTClassify
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry

/-! # Two runs of the key search's loop (x86)

Two runs at the same loop point (`LiveCT`: the public descriptor, the octets
consumed, the budgets and the statuses of the attempts still to come) branch
alike (`branch_ct`), and their next points are the same function of it
(`ct_step`), so the loop leaks the points alone (`loop_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A loop point: the loop's public data and the statuses still to come. -/
abbrev Kp := Lp × List Nat

def LiveCT (q : Kp) (s : State) : Prop :=
  ∃ o, Live q.1.1 o q.1.2.1 q.1.2.2.1 q.1.2.2.2 s ∧
    (q.1.1.tail (randOf o) q.1.2.1 q.1.2.2.1 q.1.2.2.2).statuses = q.2

theorem Live.any {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    Any p s := ⟨o, _, _, h.input.2, h.st⟩

theorem liveCT_any (q : Kp) (s : State) (h : LiveCT q s) : Any q.1.1 s := let ⟨_, L, _⟩ := h; L.any

/-- `mov eax, [esi + d]; test eax, eax` on a budget. -/
theorem budget_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s)
    {d : Nat} (hd : d = keysOff ∨ d = scalarsOff) :
    WP isa (.block [.mov .eax (.mem (st d)), .alu .test .eax (.reg .eax)]) s fun t =>
      Live p o used keys scalars t ∧
        isa.eval .e t = some (decide ((if d = keysOff then keys else scalars) = 0)) := by
  have S := h.st
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  rcases hd with rfl | rfl
  · refine S.ld (Or.inl rfl) (d := keysOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
    refine wp_test fun t₂ F₂ z₂ => WP.block_nil ⟨(S₁.fupd F₂).live hul hkl hcl, ?_⟩
    exact test_zero (k := keys) (by omega) g₁ z₂
  · refine S.ld (Or.inl rfl) (d := scalarsOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
    refine wp_test fun t₂ F₂ z₂ => WP.block_nil ⟨(S₁.fupd F₂).live hul hkl hcl, ?_⟩
    exact test_zero (k := scalars) (by omega) g₁ z₂

/-- `room`: the borrow when the tape holds less than an attempt. -/
theorem room_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa (.block room) s fun t => Live p o used keys scalars t ∧
      isa.eval .b t = some (decide (p.randLen - used < p.len)) := by
  have S := h.st
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 9).isLt
  have hL : (ofState o).len < 2 ^ 32 := (arg o 7).isLt
  unfold room
  refine S.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₅ S₅ g₅ _ _ _ => ?_
  refine S₅.ld (Or.inr (Or.inl rfl)) (d := lenOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ _ => ?_
  refine wp_cmp fun t₇ F₇ c₇ _ => WP.block_nil ⟨(S₆.fupd F₇).live hul hkl hcl, ?_⟩
  show t₇.cf = _
  rw [c₇, o₆ .eax (by decide), g₅, g₆]
  simp only [liveF, leftOff, lenOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt hL]

/-- The status of the next attempt, from the statuses still to come. -/
theorem head_status {p : KPub} {o : State} {used keys scalars : Nat} {sts : List Nat}
    (h : (p.tail (randOf o) used keys scalars).statuses = sts) (hk : keys ≠ 0) (hs : scalars ≠ 0)
    (hr : p.len ≤ (randOf o).length - used) : attemptStatus p.a p.len ((randOf o).drop used) = sts.headD 0 := by
  have := keyTail_statuses_head (a := p.a) (len := p.len) (rand := randOf o) (used := used) hk hs hr
  rw [KPub.tail] at h
  rw [h] at this
  cases sts with
  | nil => cases this
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at this; simp [this]

theorem rand_length {o : State} : (randOf o).length = (ofState o).randLen := by
  simp only [randOf, Spec.Rsa.bytesAt, List.length_map, List.length_range]; rfl

theorem ne_of_eval {s : State} {b : Prop} [Decidable b] (h : isa.eval .e s = some (decide b))
    (hf : isa.eval .e s = some false) : ¬ b := by
  rw [h] at hf; simpa using hf

theorem branch_ct : RelCT isa (Two LiveCT) branch fun _ _ => True := by
  unfold branch
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveCT q t ∧ isa.eval .e t = some (decide (q.1.2.2.1 = 0)))
    [.esi, .esp] (any_pins (fun q => q.1.1) liveCT_any) (by taint_decide)
    fun q s ⟨o, L, hs⟩ => WP.mono (budget_ok L (Or.inl rfl)) fun t ⟨L', e⟩ => ⟨⟨o, L', hs⟩, by simpa using e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨o, L, _⟩, _⟩, _⟩ => L.at) exhausted_ct) ?_
  refine RelCT.seq (two_piece (Ψ := fun q t => (LiveCT q t ∧ q.1.2.2.1 ≠ 0) ∧
      isa.eval .e t = some (decide (q.1.2.2.2 = 0)))
    [.esi, .esp] (any_pins (fun q => q.1.1) fun q s h => liveCT_any q s h.1.1) (by taint_decide)
    fun q s ⟨⟨⟨o, L, hs⟩, e⟩, hf⟩ => WP.mono (budget_ok L (Or.inr rfl)) fun t ⟨L', e'⟩ =>
      ⟨⟨⟨o, L', hs⟩, ne_of_eval e hf⟩, by simpa [scalarsOff, keysOff] using e'⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨⟨o, L, _⟩, _⟩, _⟩, _⟩ => L.at) exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece (Ψ := fun q t => (LiveCT q t ∧ q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0) ∧
      isa.eval .b t = some (decide (q.1.1.randLen - q.1.2.1 < q.1.1.len)))
    [.esi, .esp] (any_pins (fun q => q.1.1) fun q s h => liveCT_any q s h.1.1.1) (by taint_decide)
    fun q s ⟨⟨⟨⟨o, L, hs⟩, hk⟩, e⟩, hf⟩ => WP.mono (room_ok L) fun t ⟨L', e'⟩ =>
      ⟨⟨⟨o, L', hs⟩, hk, ne_of_eval e hf⟩, e'⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨⟨o, L, _⟩, _⟩, _⟩, _⟩ => L.at) request_ct) ?_
  -- The attempt, with the status the statuses still to come begin with.
  have hatt : ∀ (q : Kp) s, ((LiveCT q s ∧ q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0) ∧
      isa.eval .b s = some (decide (q.1.1.randLen - q.1.2.1 < q.1.1.len))) ∧ isa.eval .b s = some false →
      AttAt (q.1, q.2.headD 0) s := by
    intro q s h
    obtain ⟨⟨⟨⟨o, L, hs⟩, hk, hc⟩, e⟩, hf⟩ := h
    rw [e] at hf
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hf
    have hp := L.input.2
    have hr : q.1.1.len ≤ (randOf o).length - q.1.2.1 := by rw [← hp, rand_length, hp]; exact hf
    have hu := L.used_le
    exact ⟨o, L, by dsimp only; omega, head_status hs hk hc hr⟩
  refine RelCT.seq (two_post (Ψ := fun q t => ClsAt (q.1, q.2.headD 0) t)
    (two_map (fun q => (q.1, q.2.headD 0)) hatt attempt_ct) fun q s h => ?_)
    (two_map (fun q => (q.1, q.2.headD 0)) (fun _ _ h => h) classify_ct)
  obtain ⟨o, L, hu, st⟩ := hatt q s h
  dsimp only at L hu st
  have hp := L.input.2
  have hc := attemptStatus_cases q.1.1.a q.1.1.len ((randOf o).drop q.1.2.1)
  refine WP.mono (attempt_ok L hu) fun u ⟨Su, eu, _⟩ => ⟨o, hp, Su, by rw [eu, st], ?_, hu⟩
  dsimp only; rw [← st]; omega

end VG.Proof.Ffdh.X86.KeySearch
