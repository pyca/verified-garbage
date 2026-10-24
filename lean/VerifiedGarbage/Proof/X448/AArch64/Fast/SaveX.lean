module

public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
import VerifiedGarbage.Proof.Framework.Range

/-! Saving and restoring GPRs without importing the X448 ladder's arithmetic. -/

@[expose] public section
namespace VG.Proof.X448.AArch64.Fast
open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Impl.X448.AArch64.Fast (SAVE saved save restore)
open VG.Proof.X448.AArch64 (Keeps Scr word Outside Outside2)
open VG.Proof.Curve448.AArch64.Fast (stw_ok ld_ok)

/-- `x21`–`x28` saved in the working space. -/
def SavedX (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ k < 8, word m base (SAVE + 8 * k) = g (saved k)

theorem SavedX.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : SavedX base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ SAVE) (hy : SAVE + 64 ≤ y) :
    SavedX base g m' := fun k hk =>
  (ho.word (Or.inr (by omega)) (Or.inl (by omega)) (by simp only [SAVE]; omega)).trans (h k hk)

theorem SavedX.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : SavedX base g m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ SAVE ∨ SAVE + 64 ≤ o) :
    SavedX base g m' := fun k hk =>
  (ho.word (by omega) (by simp only [SAVE]; omega)).trans (h k hk)

theorem saved_ne : ∀ k < 8, saved k ≠ .x3 ∧ saved k ≠ .x12 := by decide

theorem save_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block save) s fun t =>
      SavedX base s.gpr t.mem ∧ Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have e : save = (List.range 8).flatMap fun k => [st (saved k) (SAVE + 8 * k)] := by
    simp only [save]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, word t.mem base (SAVE + 8 * k) = s.gpr (saved k)) ∧
    Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl⟩
  have ts : Scr t base := ⟨by rw [tg]; exact hs.x3, by rw [tg]; exact hs.mask, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (stw_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uw, uO, ug, ur, uwr⟩ => ⟨fun k hk => ?_,
      tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr, uwr.trans tw⟩
  rw [uw _ (by simp only [SAVE]; omega) (by omega)]
  by_cases h : k = n
  · subst h; rw [ite_eq_left rfl, tg]
  · rw [ite_eq_right (by omega)]; exact tv k (by omega)

theorem restoreX_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : SavedX base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t := by
  have e : restore = (List.range 8).flatMap fun k => [ld (saved k) (SAVE + 8 * k)] := by
    simp only [restore]; rfl
  rw [e]
  have sinj : ∀ k < 8, ∀ j < 8, j ≠ k → saved j ≠ saved k := by decide
  have smem : ∀ k < 8, saved k ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide
  let inv := fun n (t : State) =>
    (∀ k < n, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (ld_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uv, um, uk⟩ => ⟨fun k hk => ?_, um.trans tm, tk.trans (uk.mono ?_)⟩
  · by_cases h : k = n
    · subst h; rw [uv, tm]; exact hsv k hn
    · rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sinj n hn k (by omega) h)]
      exact tv k (by omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [hr]; exact smem n hn

end VG.Proof.X448.AArch64.Fast
