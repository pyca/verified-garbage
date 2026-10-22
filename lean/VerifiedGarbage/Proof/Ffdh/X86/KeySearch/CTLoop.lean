module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTClassify
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTClassify
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Data
public import VerifiedGarbage.Proof.Framework.RelCT

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

theorem Done.any {p : KPub} {o s : State} {r : KeySearchResult} (h : Done p o r s) : Any p s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, _, _, rfl, ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩⟩

theorem iteration_ct : RelCT isa (Two LiveCT) iteration fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_post (Ψ := fun q t => Any q.1.1 t) branch_ct fun q s ⟨o, L, _⟩ => WP.mono (branch_ok L)
    fun v hv => ?_) (two_taint [.esi, .esp] (any_pins (fun q => q.1.1) fun _ _ h => h) (by taint_decide))
  rcases hv with ⟨D, _⟩ | ⟨_, _, _, ⟨_, R, _⟩ | ⟨_, R, _⟩⟩
  · exact D.any
  · exact R.any
  · exact R.any

/-- Whether the loop goes on after an iteration from `q`: an attempt was made and rejected. -/
def Kp.cont (q : Kp) : Prop :=
  q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0 ∧ q.1.2.1 + q.1.1.len ≤ q.1.1.randLen ∧ (q.2.headD 0 = 2 ∨ q.2.headD 0 = 3)

instance (q : Kp) : Decidable q.cont := inferInstanceAs (Decidable (_ ∧ _))

/-- The loop point after a rejection. -/
def Kp.next (q : Kp) : Kp :=
  if q.2.headD 0 = 2 then ((q.1.1, q.1.2.1 + q.1.1.len, q.1.2.2.1, q.1.2.2.2 - 1), q.2.tail)
  else ((q.1.1, q.1.2.1 + q.1.1.len, q.1.2.2.1 - 1, 128), q.2.tail)

def CTStep (q : Kp) (s : State) : Prop :=
  if q.cont then isa.eval .e s = some true ∧ LiveCT q.next s else isa.eval .e s = some false

theorem ct_step (q : Kp) (s : State) (h : LiveCT q s) : WP isa iteration s (CTStep q) := by
  obtain ⟨⟨p, used, keys, scalars⟩, sts⟩ := q
  obtain ⟨o, L, hs⟩ := h
  dsimp only at L hs
  have hp := L.input.2
  have hlen : (randOf o).length = p.randLen := by rw [← hp, rand_length]
  unfold iteration
  refine WP.seq (WP.mono (branch_ok L) fun v hv => ?_)
  rcases hv with ⟨D, stop⟩ | ⟨hk, hc, hr, ⟨h2, R⟩ | ⟨h3, R⟩⟩
  · refine WP.mono (guard_done D) fun t ⟨he, _⟩ => ?_
    have nc : ¬ Kp.cont ((p, used, keys, scalars), sts) := by
      intro hco
      obtain ⟨hk, hc, hr, h23⟩ := hco
      dsimp only at hk hc hr h23
      refine stop ⟨hk, hc, hr, ?_⟩
      rw [head_status hs hk hc (by rw [hlen]; omega)]
      exact h23
    simp only [CTStep, nc, ite_false]
    exact he
  · refine WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => ?_
    have e2 : sts.headD 0 = 2 := by rw [← head_status hs hk hc (by rw [hlen]; omega)]; exact h2
    have co : Kp.cont ((p, used, keys, scalars), sts) := ⟨hk, hc, hr, Or.inl e2⟩
    simp only [CTStep, co, ite_true, Kp.next, e2]
    refine ⟨he, o, Lt, ?_⟩
    have := hs
    show (keyTail _ _ _ _ _ _).statuses = sts.tail
    rw [KPub.tail, keyTail_scalar hk hc (by rw [hlen]; omega) h2] at this
    rw [← this]; rfl
  · refine WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => ?_
    have e3 : sts.headD 0 = 3 := by rw [← head_status hs hk hc (by rw [hlen]; omega)]; exact h3
    have co : Kp.cont ((p, used, keys, scalars), sts) := ⟨hk, hc, hr, Or.inr e3⟩
    simp only [CTStep, co, ite_true, Kp.next, e3]
    refine ⟨he, o, Lt, ?_⟩
    have := hs
    show (keyTail _ _ _ _ _ _).statuses = sts.tail
    rw [KPub.tail, keyTail_public hk hc (by rw [hlen]; omega) h3] at this
    rw [← this]; rfl

/-- The loop's measure. -/
def Kp.measure (q : Kp) : Nat := 129 * q.1.2.2.1 + q.1.2.2.2

theorem Kp.next_measure {q : Kp} (h : q.cont) : q.next.measure < q.measure := by
  obtain ⟨hk, hc, _, _⟩ := h
  unfold Kp.next Kp.measure
  split <;> dsimp only <;> omega

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : Kp, n = q.measure ∧ LiveCT q s ∧ LiveCT q t

private theorem iteration_pair (n : Nat) :
    RelCT isa (LoopPair n) iteration fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hc := two_post (Φ := fun (q : Kp) s => n = q.measure ∧ LiveCT q s)
    (Ψ := fun q t => n = q.measure ∧ CTStep q t) (iteration_ct.mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : q.cont
  · simp only [CTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ⟨q.next.measure, ?_, q.next, rfl, h₁.2, h₂.2⟩⟩
    rw [hn]; exact Kp.next_measure hb
  · simp only [CTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    have : isa.eval .e s = some false := h₁
    rw [this] at ht
    cases ht

theorem loop_ct : RelCT isa (Two LiveCT) (.loop iteration .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration) (c := .e) (Q := fun _ _ => True) LoopPair iteration_pair
    q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86.KeySearch
