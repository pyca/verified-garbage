import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Mash

/-!
# The sixteen reverse rounds on eight blocks

`rounds_ok`: on both sets, the reverse rounds of `Spec.Rc2.decryptBlock`.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Word `i` of both sets reverse mashed. -/
theorem mashStep_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) {i : Nat} (hi : i < 4) :
    ∃ s', runBlock isa (rmash 0 i ++ rmash 1 i) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      VKeep s s' := by
  obtain ⟨s₁, r₁, w₁, o₁, k₁, sp₁⟩ := rmash_ok hs (h := 0) (by decide) hi (hv 0 (by decide))
  have f₀ := regs_fixed 0 i (by decide) hi
  have sch₁ : ∀ r < 8, s₁.v (treg r) = s.v (treg r) := by
    intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    exact o₁ _ (f₀.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5
  have v₁ : VWords s₁ 1 (fun b => vs (4 * 1 + b)) := (hv 1 (by decide)).keep fun i' hi' => by
    have wn := wreg_ne 1 i' (by decide)
    exact o₁ _ (regs_cross 0 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  obtain ⟨s₂, r₂, w₂, o₂, k₂, sp₂⟩ :=
    rmash_ok (fun r hr => (sch₁ r hr).trans (hs r hr)) (h := 1) (by decide) hi v₁
  have f₁ := regs_fixed 1 i (by decide) hi
  have w₂' : VWords s₂ 0 (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i
      (vs (4 * 0 + b))) := w₁.keep fun i' hi' => by
    have wn := wreg_ne 0 i' (by decide)
    exact o₂ _ (regs_cross 1 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  refine ⟨s₂, runBlock_cat_some r₁ r₂, fun h hh => ?_, ⟨k₁.trans k₂, by rw [sp₂, sp₁], ?_, ?_⟩⟩
  · match h, hh with
    | 0, _ => exact w₂'
    | 1, _ => exact w₂
  · intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [o₂ _ (f₁.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5]
    exact sch₁ r hr
  · rw [o₂ _ f₁.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      o₁ _ f₀.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem mashSteps_ok {m : Mem} {p : Addr} (is : List Nat) (his : ∀ i ∈ is, i < 4) {s : State}
    (hs : SchedV s m p) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => rmash 0 i ++ rmash 1 i) s = some s' ∧
      Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i r) (vs b)) ∧
      VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := mashStep_ok hs hv (his i (by simp))
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmashRound_ok {m : Mem} {p : Addr} {s : State} (hs : SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa rmashRound s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMashRound (Spec.Rc2.scheduleAt m p) (vs b)) ∧
      VKeep s s' :=
  mashSteps_ok [3, 2, 1, 0] (by decide) hs hv

/-- A reverse round of `Spec.Rc2.decryptBlock`: the mixing round `15 - j`,
then the mashing round after the fifth and the eleventh. -/
def revRound (k : Spec.Rc2.Schedule) (r : Spec.Rc2.State) (j : Nat) : Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then Spec.Rc2.reverseMashRound k (Spec.Rc2.reverseMixRound k (15 - j) r)
  else Spec.Rc2.reverseMixRound k (15 - j) r

theorem roundsList_ok {m : Mem} {p : Addr} (js : List Nat) {s : State} (hs : SchedV s m p)
    (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (js.flatMap fun j =>
        rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
      Sets s' (fun b => js.foldl (revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VKeep s s' := by
  induction js generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons j js ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := rmixRound_ok (j := 15 - j) (by omega) hs hm hv
    have step : ∃ s', runBlock isa
        (rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
        Sets s' (fun b => revRound (Spec.Rc2.scheduleAt m p) (vs b) j) ∧ VKeep s s' := by
      by_cases hc : j = 4 ∨ j = 10
      · obtain ⟨s₂, r₂, v₂, k₂⟩ := rmashRound_ok (hs.keep k₁) v₁
        refine ⟨s₂, ?_, fun h hh i hi b hb => ?_, k₁.trans k₂⟩
        · simp only [hc, ↓reduceIte]; exact runBlock_cat_some r₁ r₂
        · simp only [revRound, hc, ↓reduceIte]; exact v₂ h hh i hi b hb
      · refine ⟨s₁, ?_, fun h hh i hi b hb => ?_, k₁⟩
        · simp only [hc, ↓reduceIte, List.append_nil]; exact r₁
        · simp only [revRound, hc, ↓reduceIte]; exact v₁ h hh i hi b hb
    obtain ⟨s₂, r₂, v₂, k₂⟩ := step
    obtain ⟨s₃, r₃, v₃, k₃⟩ := ih (hs.keep k₂) (k₂.mask.trans hm) v₂
    exact ⟨s₃, by rw [List.flatMap_cons]; exact runBlock_cat_some r₂ r₃, v₃, k₂.trans k₃⟩

theorem revRounds_eq (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    Spec.Rc2.decryptBlock k b =
      Spec.Rc2.encodeBlock ((List.range 16).foldl (revRound k) (Spec.Rc2.decodeBlock b)) := by
  simp only [Spec.Rc2.decryptBlock]
  rfl

theorem rounds_ok {m : Mem} {p : Addr} {s : State} (hs : SchedV s m p)
    (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa rounds s = some s' ∧
      Sets s' (fun b => (List.range 16).foldl (revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VKeep s s' :=
  roundsList_ok _ hs hm hv

end VG.Proof.Rc2.AArch64.Vec
