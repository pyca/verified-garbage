module

public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Exec
import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Convert
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude

/-! ### `X448.AArch64.Fast.SaveX`, which the modules that import this one used -/

section

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
  (ho.word (Or.inr (by omega_using [hx])) (Or.inl (by omega_using [hy, hk])) (by simp only [SAVE]; omega_using [hk])).trans (h k hk)

theorem SavedX.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : SavedX base g m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ SAVE ∨ SAVE + 64 ≤ o) :
    SavedX base g m' := fun k hk =>
  (ho.word (by omega_using [hx, hk]) (by simp only [SAVE]; omega_using [hk])).trans (h k hk)

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
  refine WP.mono (stw_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega_using [])
    (by simp only [SAVE]; omega_using [hn])) fun u ⟨uw, uO, ug, ur, uwr⟩ => ⟨fun k hk => ?_,
      tO.trans (uO.mono (by omega_using []) (by omega_using [hn])), ug.trans tg, ur.trans tr, uwr.trans tw⟩
  rw [uw _ (by simp only [SAVE]; omega_using [hn, hk]) (by omega_using [])]
  by_cases h : k = n
  · subst h; rw [ite_eq_left rfl, tg]
  · rw [ite_eq_right (by omega_using [h])]; exact tv k (by omega_using [hk, h])

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
  refine WP.mono (ld_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega_using [])
    (by simp only [SAVE]; omega_using [hn])) fun u ⟨uv, um, uk⟩ => ⟨fun k hk => ?_, um.trans tm, tk.trans (uk.mono ?_)⟩
  · by_cases h : k = n
    · subst h; rw [uv, tm]; exact hsv k hn
    · rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sinj n hn k (by omega_using [hn, hk]) h)]
      exact tv k (by omega_using [hk, h])
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [hr]; exact smem n hn

end VG.Proof.X448.AArch64.Fast

end

end

/-!
# X448 on AArch64: saving `v8`–`v15`

Untrusted: everything here is checked by Lean. The AdvSIMD products use
every vector register, so the function saves `v8`–`v15` (whose low halves
are callee-saved) at `VSAVE`, past everything else it writes, and restores
them last.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Fast (VSAVE vsave vrestore)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write scr_of setMem setMem_mem V_ne)
open VG.Proof.X448.AArch64 (Scr off Outside Outside2 FieldMem ofs)
open VG.Proof.X448.AArch64.Weak (ofs_off')

theorem _root_.VG.Proof.X448.AArch64.Outside.read16 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 8192) :
    m'.read (off base d) 16 = m.read (off base d) 16 :=
  (Mem.read_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd', hi])]; omega_using [hd, hi])).symm).symm

/-- The low halves of `v8`–`v15` of `v`, saved in the working space. -/
def SavedV (base : Addr) (v : VReg → BitVec 128) (m : Mem) : Prop :=
  ∀ k < 8, (m.read (off base (VSAVE + 16 * k)) 16).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64

theorem SavedV.frame {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    (he : ∀ d, VSAVE ≤ d → d < VSAVE + 128 → m' (off base d) = m (off base d)) : SavedV base v m' := by
  intro k hk
  rw [← h k hk, Mem.read_congr fun i hi => ?_]
  have hV : VSAVE = 4736 := rfl
  rw [off_add]
  exact he _ (by omega_using []) (by omega_using [hk, hi])

theorem SavedV.outside2 {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ VSAVE) (hy : y + ny ≤ VSAVE) :
    SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega_using [h2])]; omega_using [hx, h1])
    (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega_using [h2])]; omega_using [hy, h1])

theorem SavedV.outside {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ VSAVE ∨ VSAVE + 128 ≤ o) : SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega_using [h2])]; omega_using [hx, h1, h2])

theorem SavedV.field {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {o : Nat} (ho : FieldMem base o m m') (hx : o + 128 ≤ VSAVE) : SavedV base v m' := by
  have hA : ACC = 3584 := rfl
  have hV : VSAVE = 4736 := rfl
  exact h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by omega_using [hV, h2])]; omega_using [hx, h1])
    (by rw [ofs_off' base (by omega_using [hV, h2])]; omega_using [hA, hV, h1])

/-- Away from the output: `hfar` as `output_word` takes it. -/
theorem SavedV.output {base p : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {n : Nat} (ho : Outside p 0 n m m') (hn : n ≤ 56) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (Or.inr (Nat.le_trans (by omega_using [hn]) (hfar d (by simp only [VSAVE] at h2; omega_using [h2]))))

theorem vsave_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vsave) s fun t =>
      SavedV base s.v t.mem ∧ Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vsave = (List.range 8).flatMap fun k => [stq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vsave]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (VSAVE + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tvv, tr, tw⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, _, tr, tw⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tr, tw⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := VSAVE + 16 * n) (by omega_using [hV]) (by omega_using [hV, hn]),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega_using [hV, hn])).mono (by omega_using []) (by omega_using [hn])),
      tg, tvv, tr, tw⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := VSAVE + 16 * n) (by omega_using [hV, hn]))).read16 (by omega_using [h])
      (by omega_using [hV, hn, hk])]
    exact tv k (by omega_using [hk, h])

theorem vrestore_ok {s : State} {base : Addr} (hs : Scr s base) {v : VReg → BitVec 128}
    (hsv : SavedV base v s.mem) :
    WP isa (.block vrestore) s fun t =>
      (∀ k < 8, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vrestore = (List.range 8).flatMap fun k => [ldq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vrestore]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := VSAVE + 16 * n) (by omega_using [hV]) (by omega_using [hV, hn]),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]; exact hsv k hn
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_using [hn, hk]) _ (by omega_using [hn]) (by omega_using [h]))]
    exact tv k (by omega_using [hk, h])

end VG.Proof.X448.AArch64.Fast
