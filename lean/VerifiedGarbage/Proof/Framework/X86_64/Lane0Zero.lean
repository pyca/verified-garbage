module

public import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# x86-64: `VEX.128` blocks keep cleared upper lanes cleared

A `VEX.128` instruction clears lanes 1–3 of its destination and keeps those
of every other register, so an upper lane that is clear before a block of
them (`lane0Block`) is clear after it (`lane0Block_zhi`, `WP.lane0z`).
-/

@[expose] public section

namespace VG.X86_64

theorem setV128_zhi (s : State) (d r : XReg) (lo hi : BitVec 128) {l : Nat} (hl1 : 1 ≤ l) (hl4 : l < 4)
    (hz : s.zlane r l = 0) : (s.setV .l128 d lo hi).zlane r l = 0 := by
  rw [State.zlane_setV128 _ _ _ _ _ hl4]
  split
  · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
  · exact hz

/-- An instruction of `lane0V` writes its destination as `VEX.128`. -/
theorem lane0V_setV {o : VOp} {ss : List Instr} (h : lane0V o = some ss) (s : State) :
    ∃ d lo hi, VOp.exec o s = s.setV .l128 d lo hi := by
  cases o
  all_goals try (simp only [lane0V, reduceCtorEq] at h)
  case vbin op len d a b =>
    cases len
    · exact ⟨d, op.sse.eval (s.lane a 0) (s.lane b 0), op.sse.eval (s.lane a 1) (s.lane b 1), rfl⟩
    · simp at h
  case vpclmulqdq len d a b n =>
    cases len
    · exact ⟨d, pclmul (s.lane a 0) (s.lane b 0) n, pclmul (s.lane a 1) (s.lane b 1) n, rfl⟩
    · simp at h
  case vmovdqa len d r =>
    cases len
    · exact ⟨d, s.lane r 0, s.lane r 1, rfl⟩
    · simp at h
  case vshift op len d r n =>
    cases len
    · exact ⟨d, op.eval (s.lane r 0) n, op.eval (s.lane r 1) n, rfl⟩
    · simp at h
  case vpshufd len d r o =>
    cases len
    · exact ⟨d, shufDwords (s.lane r 0) o, shufDwords (s.lane r 1) o, rfl⟩
    · simp at h
  case vmovq d r => exact ⟨d, (0 : BitVec 64) ++ s.gpr r, 0, rfl⟩

theorem lane0_zhi {i : Instr} {ss : List Instr} (h : lane0 i = some ss) {s s' : State}
    (e : exec i s = some s') (r : XReg) {l : Nat} (hl1 : 1 ≤ l) (hl4 : l < 4) (hz : s.zlane r l = 0) :
    s'.zlane r l = 0 := by
  cases i
  all_goals try (simp only [lane0, reduceCtorEq] at h)
  case movImm64 d v => cases e; exact hz
  case vmovdquLoad len d m =>
    cases len
    · simp only [exec, Option.map_eq_some_iff] at e
      obtain ⟨v, -, rfl⟩ := e
      exact setV128_zhi _ _ _ _ _ hl1 hl4 hz
    · simp at h
  case vmovdquStore len m r' =>
    cases len
    · simp only [exec, State.store128] at e
      split at e
      · cases e; exact hz
      · cases e
    · simp at h
  case vop o =>
    simp only [exec, Option.some.injEq] at e
    subst e
    obtain ⟨d, lo, hi, he⟩ := lane0V_setV h s
    rw [he]
    exact setV128_zhi _ _ _ _ _ hl1 hl4 hz

theorem lane0Block_zhi {vs ss : List Instr} (h : lane0Block vs = some ss) {s s' : State}
    (e : runBlock isa vs s = some s') (r : XReg) {l : Nat} (hl1 : 1 ≤ l) (hl4 : l < 4)
    (hz : s.zlane r l = 0) : s'.zlane r l = 0 := by
  induction vs generalizing ss s with
  | nil => cases e; exact hz
  | cons i is ih =>
    simp only [lane0Block] at h
    split at h
    · rename_i a b ha hb
      cases h
      have e₀ : (exec i s).bind (runBlock isa is) = some s' := e
      cases e₁ : exec i s with
      | none => rw [e₁] at e₀; cases e₀
      | some s₁ =>
        rw [e₁, Option.bind_some] at e₀
        exact ih hb e₀ (lane0_zhi ha e₁ r hl1 hl4 hz)
    · cases h

theorem setV128_zkeep (s : State) {d r : XReg} (hr : d ≠ r) (lo hi : BitVec 128) {l : Nat} (hl4 : l < 4) :
    (s.setV .l128 d lo hi).zlane r l = s.zlane r l := by
  rw [State.zlane_setV128 _ _ _ _ _ hl4, ite_eq_right_iff.2 (fun h => absurd h.symm hr)]

/-- An instruction of `lane0` keeps every lane of the registers it does not write. -/
theorem lane0_zkeep {i : Instr} {ss : List Instr} (h : lane0 i = some ss) {s s' : State}
    (e : exec i s = some s') (r : XReg) (hr : vdst i ≠ some r) {l : Nat} (hl4 : l < 4) :
    s'.zlane r l = s.zlane r l := by
  cases i
  all_goals try (simp only [lane0, reduceCtorEq] at h)
  case movImm64 d v => cases e; rfl
  case vmovdquLoad len d m =>
    have hrd : d ≠ r := fun h => hr (by rw [h]; rfl)
    cases len
    · simp only [exec, Option.map_eq_some_iff] at e
      obtain ⟨v, -, rfl⟩ := e
      exact setV128_zkeep _ hrd _ _ hl4
    · simp at h
  case vmovdquStore len m r' =>
    cases len
    · simp only [exec, State.store128] at e
      split at e
      · cases e; rfl
      · cases e
    · simp at h
  case vop o =>
    simp only [exec, Option.some.injEq] at e
    subst e
    cases o
    all_goals try (simp only [lane0V, reduceCtorEq] at h)
    case vbin op len d a b =>
      cases len
      · simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4
      · simp at h
    case vpclmulqdq len d a b n =>
      cases len
      · simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4
      · simp at h
    case vmovdqa len d r' =>
      cases len
      · simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4
      · simp at h
    case vshift op len d r' n =>
      cases len
      · simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4
      · simp at h
    case vpshufd len d r' o =>
      cases len
      · simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4
      · simp at h
    case vmovq d r' => simp only [VOp.exec]; exact setV128_zkeep _ (fun h => hr (by rw [h]; rfl)) _ _ hl4

theorem lane0Block_zkeep {vs ss : List Instr} (h : lane0Block vs = some ss) {s s' : State}
    (e : runBlock isa vs s = some s') (r : XReg) (hr : r ∉ vs.filterMap vdst) {l : Nat} (hl4 : l < 4) :
    s'.zlane r l = s.zlane r l := by
  induction vs generalizing ss s with
  | nil => cases e; rfl
  | cons i is ih =>
    simp only [lane0Block] at h
    split at h
    · rename_i a b ha hb
      cases h
      have e₀ : (exec i s).bind (runBlock isa is) = some s' := e
      cases e₁ : exec i s with
      | none => rw [e₁] at e₀; cases e₀
      | some s₁ =>
        rw [e₁, Option.bind_some] at e₀
        have hr' : vdst i ≠ some r ∧ r ∉ is.filterMap vdst := by
          constructor
          · intro hv; exact hr (by simp [hv])
          · intro hm; exact hr (by cases hv : vdst i <;> simp [hv] at hm ⊢ <;> simp_all)
        rw [ih hb e₀ hr'.2, lane0_zkeep ha e₁ r hr'.1 hl4]
    · cases h

/-- `WP.lane0`, and the upper lanes cleared before the block cleared after it. -/
theorem WP.lane0z {vs ss : List Instr} (h : lane0Block vs = some ss) {s : State} {Q : State → Prop}
    (hq : WP isa (.block ss) (s.proj 0) Q) :
    WP isa (.block vs) s fun s' => Q (s'.proj 0) ∧ (vs.all noGpr = true → s'.gpr = s.gpr) ∧
      (∀ r l, 1 ≤ l → l < 4 → s.zlane r l = 0 → s'.zlane r l = 0) ∧
      (∀ r, r ∉ vs.filterMap vdst → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  obtain ⟨t, et, qt⟩ := WP.runBlock_of hq
  have e := lane0Block_ok h s
  rw [et] at e
  cases e' : runBlock isa vs s with
  | none => rw [e'] at e; cases e
  | some s' =>
    rw [e'] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact WP.of_runBlock ⟨s', e', e ▸ qt, fun hn => lane0Block_gpr h hn e',
      fun r l h1 h4 hz => lane0Block_zhi h e' r h1 h4 hz, fun r hr l hl => lane0Block_zkeep h e' r hr hl⟩

end VG.X86_64
