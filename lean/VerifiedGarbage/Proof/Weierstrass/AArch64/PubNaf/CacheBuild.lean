module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Cache
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CoZField
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Building the cache

Entry `a`'s `z` into `t2`, its square into `t0` and cube into `t1` (on the
co-Z programs' slots, `coZσ`: `2`, `3` and `4`), and both into the cache
(`cacheOne_ok`); entries `1 … m` in turn (`cacheTo_ok`), keeping the table.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The square and cube on numbered slots: `2 = 4²`, `3 = 4 · 2`. -/
def cubeN : List FOp := [.mul 2 4 4, .mul 3 4 2]

theorem cubeN_out : ∀ op ∈ cubeN, op.out < 11 := by decide
theorem cubeN_reads : readsOk cubeN [4] = true := by decide

theorem cubeN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps cubeN e 2 = e 4 * e 4 ∧ runOps cubeN e 3 = e 4 * (e 4 * e 4) := ⟨rfl, rfl⟩

theorem cube_eq (K : WinCfg) :
    [FOp.mul K.S.t0 K.S.t2 K.S.t2, .mul K.S.t1 K.S.t2 K.S.t0] = cubeN.map (CoZ.rename (coZσ K)) := rfl

/-- Words of the table survive changes away from it. -/
theorem tbl_away {K : WinCfg} {size m : Nat} (hL : WinLay K size) (hC : CacheLay K size)
    {base : Addr} {mm mm' : Mem} {W : List (Nat × Nat)} (hU : Unch base W mm mm') (hW : Away K m W)
    (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 24) :
    wordsVal mm' base (K.tbl + 8 * K.M.n * i) K.M.n = wordsVal mm base (K.tbl + 8 * K.M.n * i) K.M.n := by
  have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
    simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
  refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega_using [hn, this])
  rcases hW w hw with ⟨-, ht⟩ | hw1
  · exact ht i hi
  · left
    have := hC.slots _ hs
    have : cacheAt K 1 ≤ cacheAt K (m + 1) := by rw [cacheAt_eq K (m + 1)]; omega
    omega

theorem OddTbl.away {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat} (hL : WinLay K size)
    (hC : CacheLay K size) {P : Point C} {s s' : State} (hT : OddTbl K C base P 8 s)
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem) (hW : Away K m W)
    (hn : base.toNat + size ≤ 2 ^ 64) : OddTbl K C base P 8 s' := by
  intro j h1 h8
  have T := hT j h1 h8
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
    exact tbl_away hL hC hU hW hn hi
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- Entry `a`'s `Z²` and `Z³` into the cache. -/
theorem cacheOne_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {P : Point C} {u : State}
    (hs : Scr u base size) (hM : ModOkA K.M size C.p u.mem base) (hT : OddTbl K C base P 8 u)
    {a : Nat} (ha1 : 1 ≤ a) (ha8 : a ≤ 8) :
    WP isa (cacheOne K a) u fun v =>
      Scr v base size ∧ KeepRegs (nafClob K.M.n) u v ∧
      Unch base ([(cacheAt K a, 16 * K.M.n)] ++ loopW K) u.mem v.mem ∧
      ModOkA K.M size C.p v.mem base ∧
      wordsVal v.mem base (cacheAt K a) K.M.n < C.p ∧
      wordsVal v.mem base (cacheAt K a + 8 * K.M.n) K.M.n < C.p ∧
      tmv C K.M.n base v (cacheAt K a) =
        tmv C K.M.n base u (K.tblPt a).z * tmv C K.M.n base u (K.tblPt a).z ∧
      tmv C K.M.n base v (cacheAt K a + 8 * K.M.n) =
        tmv C K.M.n base u (K.tblPt a).z *
          (tmv C K.M.n base u (K.tblPt a).z * tmv C K.M.n base u (K.tblPt a).z) := by
  have hW := hL.win
  have hC := hL.cache
  have hn := hs.nowrap
  have hn0 := hW.n0
  have hz : (K.tblPt a).z ∈ winSlots K := tbl_slot ha1 ha8 _ (by simp)
  have t2s : K.S.t2 ∈ winOther K := by simp [winOther, rcbW]
  have t0s : K.S.t0 ∈ winOther K := by simp [winOther, rcbW]
  have t1s : K.S.t1 ∈ winOther K := by simp [winOther, rcbW]
  -- `t2 = z`.
  rw [cacheOne]
  refine WP.seq (WP.mono (copyField_ok hW.lay hL.al.al
    (inv_of hs hM (V := [(K.tblPt a).z]) (fun x hx => by simp at hx; subst hx; exact hz)
      (fun x hx => by simp at hx; subst hx; exact (hT a ha1 ha8).1 _ (by simp)))
    (winOther_mem t2s) (List.mem_singleton_self _)) fun u₁ ⟨k₁, I₁⟩ => ?_)
  -- `t0 = z²`, `t1 = z³`.
  rw [cube_eq]
  refine WP.seq (WP.mono (coZ_ok hL hp (coZσ_ren hW) cubeN_out cubeN_reads I₁
    (by intro i hi; simp at hi; subst hi; exact List.mem_cons_self ..)) fun u₂ ⟨k₂, U₂, I₂, e₂⟩ => ?_)
  have ve : ∀ i ∈ [2, 3], coZσ K i ∈ (cubeN.map (FOp.rename (coZσ K))).map FOp.out := by
    intro i hi
    exact out_mem (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl <;> decide)
  obtain ⟨v0, l0⟩ := written_val I₂ (ve 2 (by simp))
  obtain ⟨v1, l1⟩ := written_val I₂ (ve 3 (by simp))
  rw [e₂ 2] at v0
  rw [e₂ 3] at v1
  obtain ⟨r0, r1⟩ := cubeN_run (fun j => Function.update (tmv C K.M.n base u) K.S.t2
    (tmv C K.M.n base u (K.tblPt a).z) (coZσ K j))
  have c4 : coZσ K 4 = K.S.t2 := rfl
  simp only [c4, Function.update_self] at r0 r1
  rw [r0] at v0
  rw [r1] at v1
  change tmv C K.M.n base u₂ K.S.t0 = _ at v0
  change tmv C K.M.n base u₂ K.S.t1 = _ at v1
  change wordsVal u₂.mem base K.S.t0 K.M.n < C.p at l0
  change wordsVal u₂.mem base K.S.t1 K.M.n < C.p at l1
  -- The copies into the cache.
  have hca := cacheAt_eq K a
  have ht := hC.top
  have hm8 := Nat.mul_le_mul_left (16 * K.M.n) (show a - 1 + 1 ≤ 8 by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm8
  have lo0 := hC.slots _ (winOther_mem t0s)
  have lo1 := hC.slots _ (winOther_mem t1s)
  have le0 := hW.lay.le _ (winOther_mem t0s)
  have le1 := hW.lay.le _ (winOther_mem t1s)
  have al0 := hL.al.sl _ (winOther_mem t0s)
  have al1 := hL.al.sl _ (winOther_mem t1s)
  have alc : cacheAt K a % 8 = 0 := by
    have e16 : 16 * K.M.n * (a - 1) = 8 * (2 * K.M.n * (a - 1)) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [hca, e16]; have := hC.al; omega
  have sc₂ : Scr u₂ base size := I₂.scr
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok K.M.n sc₂ (o := cacheAt K a) (a := K.S.t0) (by omega) le0 alc al0
    (Or.inr (by omega))) fun u₃ ⟨w₃, k₃, O₃⟩ => ?_
  have sc₃ := sc₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copy_ok K.M.n sc₃ (o := cacheAt K a + 8 * K.M.n) (a := K.S.t1) (by omega) le1
    (by omega) al1 (Or.inr (by omega))) fun v ⟨w₄, k₄, O₄⟩ => ?_
  have sc₄ := sc₃.of_keepRegs k₄ (by decide)
  have U₃ := O₃.unch
  have U₄ := O₄.unch
  have t1₃ : wordsVal u₃.mem base K.S.t1 K.M.n = wordsVal u₂.mem base K.S.t1 K.M.n :=
    U₃.wordsVal (fun w hw => by simp at hw; subst hw; omega) (by omega)
  have c0₄ : wordsVal v.mem base (cacheAt K a) K.M.n = wordsVal u₃.mem base (cacheAt K a) K.M.n :=
    U₄.wordsVal (fun w hw => by simp at hw; subst hw; omega) (by omega)
  -- The frame.
  have Uall : Unch base ([(cacheAt K a, 16 * K.M.n)] ++ loopW K) u.mem v.mem := by
    have h12 : Unch base (loopW K) u.mem u₂.mem := by
      refine ((progKeep_of_op k₁ (List.mem_singleton_self _)).unch.trans U₂).mono fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        simp only [VG.Proof.Weierstrass.AArch64.loopW, List.mem_append, List.mem_map, List.mem_singleton]
        rcases hw with rfl | rfl
        · exact Or.inl ⟨_, t2s, rfl⟩
        · exact Or.inr rfl
      · exact hw
    refine (h12.trans (U₃.trans U₄)).cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(cacheAt K a, 16 * K.M.n), List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega
  have hk : KeepRegs (nafClob K.M.n) u v := by
    have kc : ∀ r ∈ [Reg.x1], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    exact (((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) u u₁).mono clob_nafClob).trans
      ((k₂.mono clob_nafClob).trans ((k₃.mono kc).trans (k₄.mono kc))))
  have hM₄ : ModOkA K.M size C.p v.mem base := hM.unch Uall (fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · simp at hw; subst hw; have := hC.mo; exact Or.inl (by simp only; omega)
    · exact winW_mo hW hM w (loopW_sub K w hw)) hn
  refine ⟨sc₄, hk, Uall, hM₄, ?_, ?_, ?_, ?_⟩
  · rw [c0₄, w₃]; exact l0
  · rw [w₄, t1₃]; exact l1
  · show toM _ _ _ = _; rw [c0₄, w₃]; exact v0
  · show toM _ _ _ = _; rw [w₄, t1₃]; exact v1

/-- Entries `1 … m` into the cache, keeping the table. -/
theorem cacheTo_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {P : Point C} {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base) (hT : OddTbl K C base P 8 s) :
    ∀ m ≤ 8, WP isa (cacheTo K m) s fun t =>
      Scr t base size ∧ KeepRegs (nafClob K.M.n) s t ∧ Unch base (cacheW K ++ loopW K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧ OddTbl K C base P 8 t ∧ CacheUpTo K C base m t
  | 0, _ => WP.block_nil ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM, hT, fun _ h1 h0 => by omega⟩
  | m + 1, hm => by
    have hW := hL.win
    have hC := hL.cache
    have hn := hs.nowrap
    rw [cacheTo]
    refine WP.seq (WP.mono (cacheTo_ok hL hp hs hM hT m (by omega))
      fun t ⟨st, kt, Ut, Mt, Tt, Ct⟩ => ?_)
    refine WP.mono (cacheOne_ok hL hp st Mt Tt (a := m + 1) (by omega) hm)
      fun v ⟨sv, kv, Uv, Mv, l0, l1, e0, e1⟩ => ?_
    have hA : Away K m ([(cacheAt K (m + 1), 16 * K.M.n)] ++ loopW K) :=
      away_append (fun w hw => by simp at hw; subst hw; exact Or.inr (Nat.le_refl _))
        (away_loopW hW hC m)
    have Tv := OddTbl.away hW hC Tt Uv hA hn
    have tz : tmv C K.M.n base v (K.tblPt (m + 1)).z = tmv C K.M.n base t (K.tblPt (m + 1)).z := by
      obtain ⟨i, hi, ez, -, -⟩ := tblPt_mem K (m := m + 1) (by omega) hm (K.tblPt (m + 1)).z (by simp)
      show toM _ _ _ = toM _ _ _; rw [ez, tbl_away hW hC Uv hA hn hi]
    refine ⟨sv, kt.trans kv, ?_, Mv, Tv, fun a h1 ha => ?_⟩
    · refine (Ut.trans Uv).cover fun w hw => ?_
      have hca := cacheAt_eq K (m + 1)
      have hm8 := Nat.mul_le_mul_left (16 * K.M.n) (show m + 1 - 1 + 1 ≤ 8 by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm8
      have hc : (cacheAt K 1, 128 * K.M.n) ∈ cacheW K ++ loopW K :=
        List.mem_append_left _ (List.mem_singleton_self _)
      simp only [cacheW, List.mem_append, List.mem_singleton] at hw
      rcases hw with (rfl | hw) | rfl | hw
      · exact ⟨_, hc, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨_, hc, ?_⟩
        simp only; omega
      · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · rcases Nat.lt_or_ge a (m + 1) with ha' | ha'
      · exact CacheUpTo.unch hW hC (by omega) Ct Uv hA hn a h1 (by omega)
      · obtain rfl : a = m + 1 := by omega
        exact ⟨l0, l1, by rw [tz]; exact e0, by rw [tz]; exact e1⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
