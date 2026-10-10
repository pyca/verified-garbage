import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacNorm
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-!
# 5-bit windows with an affine table on x86-64

`JacWinCfg.windowA` (`Impl/Weierstrass/X86_64/WinJacA.lean`) leaves `R`
representing `[k]P`, as `JacWinCfg.window` does (`winJac_ok`): the table by
`jbuild_ok`, made affine by `normA_ok` (every entry's `Z` one, `JTblOne`),
then the first digit by `jfirst_ok` and the iterations by `jstepA_ok`, which
adds the selected entry by the mixed addition (`madd_ok`, `jstepA_pt`): right
unless `R = T` (excluded for `k < n` by `Window5.loop_noexc`, as the Jacobian
addition's exceptions) or `R = O` (where `T` is kept, as before).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The mixed addition -/

/-- `R`, `T` and the slots the addition writes are apart. -/
theorem madd_apart (hL : JacWinLay K size) : RcbApart K.S K.R K.E K.D := by
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have hroW : ∀ x ∈ jwRo K ++ [K.R.x, K.R.y, K.R.z], x ∉ rcbW K.S K.D := by
    intro x hx hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases List.mem_append.mp hx with hx | hx
    · exact hL.ro x hx (by rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;>
        rcases hw with h | h | h | h | h | h | h | h | h
      all_goals first
        | exact o 0 7 (by decide) (by decide) (by decide) h | exact o 0 8 (by decide) (by decide) (by decide) h
        | exact o 0 9 (by decide) (by decide) (by decide) h | exact o 0 10 (by decide) (by decide) (by decide) h
        | exact o 0 11 (by decide) (by decide) (by decide) h | exact o 0 12 (by decide) (by decide) (by decide) h
        | exact o 0 3 (by decide) (by decide) (by decide) h | exact o 0 4 (by decide) (by decide) (by decide) h
        | exact o 0 5 (by decide) (by decide) (by decide) h
        | exact o 1 7 (by decide) (by decide) (by decide) h | exact o 1 8 (by decide) (by decide) (by decide) h
        | exact o 1 9 (by decide) (by decide) (by decide) h | exact o 1 10 (by decide) (by decide) (by decide) h
        | exact o 1 11 (by decide) (by decide) (by decide) h | exact o 1 12 (by decide) (by decide) (by decide) h
        | exact o 1 3 (by decide) (by decide) (by decide) h | exact o 1 4 (by decide) (by decide) (by decide) h
        | exact o 1 5 (by decide) (by decide) (by decide) h
        | exact o 2 7 (by decide) (by decide) (by decide) h | exact o 2 8 (by decide) (by decide) (by decide) h
        | exact o 2 9 (by decide) (by decide) (by decide) h | exact o 2 10 (by decide) (by decide) (by decide) h
        | exact o 2 11 (by decide) (by decide) (by decide) h | exact o 2 12 (by decide) (by decide) (by decide) h
        | exact o 2 3 (by decide) (by decide) (by decide) h | exact o 2 4 (by decide) (by decide) (by decide) h
        | exact o 2 5 (by decide) (by decide) (by decide) h
  have hgW : ∀ c < 5, jg K (80 + c) ∉ rcbW K.S K.D := by
    intro c hc hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have g := fun x (hx : x ∈ jwOther K) => hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega_arith)
    rcases hw with h | h | h | h | h | h | h | h | h <;> exact g _ (by jw_mem) h.symm
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    refine ⟨⟨o 7 8 (by decide) (by decide) (by decide), o 7 9 (by decide) (by decide) (by decide),
      o 7 10 (by decide) (by decide) (by decide), o 7 11 (by decide) (by decide) (by decide),
      o 7 12 (by decide) (by decide) (by decide), o 7 3 (by decide) (by decide) (by decide),
      o 7 4 (by decide) (by decide) (by decide), o 7 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 8 9 (by decide) (by decide) (by decide), o 8 10 (by decide) (by decide) (by decide),
      o 8 11 (by decide) (by decide) (by decide), o 8 12 (by decide) (by decide) (by decide),
      o 8 3 (by decide) (by decide) (by decide), o 8 4 (by decide) (by decide) (by decide),
      o 8 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 9 10 (by decide) (by decide) (by decide), o 9 11 (by decide) (by decide) (by decide),
      o 9 12 (by decide) (by decide) (by decide), o 9 3 (by decide) (by decide) (by decide),
      o 9 4 (by decide) (by decide) (by decide), o 9 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 10 11 (by decide) (by decide) (by decide), o 10 12 (by decide) (by decide) (by decide),
      o 10 3 (by decide) (by decide) (by decide), o 10 4 (by decide) (by decide) (by decide),
      o 10 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 11 12 (by decide) (by decide) (by decide), o 11 3 (by decide) (by decide) (by decide),
      o 11 4 (by decide) (by decide) (by decide), o 11 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 12 3 (by decide) (by decide) (by decide), o 12 4 (by decide) (by decide) (by decide),
      o 12 5 (by decide) (by decide) (by decide)⟩,
      ⟨o 3 4 (by decide) (by decide) (by decide), o 3 5 (by decide) (by decide) (by decide)⟩,
      o 4 5 (by decide) (by decide) (by decide), not_false⟩
  · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hroW _ (by jw_mem)
    · exact hroW _ (by jw_mem)
    · exact hroW _ (by simp)
    · exact hroW _ (by simp)
    · exact hroW _ (by simp)
    · rw [hL.Tx]; exact hgW 0 (by decide)
    · rw [hL.Ty]; exact hgW 1 (by decide)
    · rw [hL.Tz]; exact hgW 2 (by decide)

/-- `D = R + T` by the mixed addition, `T` affine (its `Z` not read). -/
theorem madd_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y], x ∈ V) :
    WP isa (.block (fprog K.M (maddJ K.S K.R K.E K.D))) s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' t ∧
        (E' K.D.x, E' K.D.y, E' K.D.z) = maddJF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) := by
  have hA := madd_apart hL
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tx, hL.Ty, hL.Tz] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hR : readsOk (maddJ K.S K.R K.E K.D) V = true := by
    rw [maddJ_eq]
    refine readsOk_mono (readsOk_rename (rcbσ K.S K.R K.E K.D)
      (show readsOk maddJN [11, 12, 13, 14, 15] = true by decide)) fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h <;> rw [h] <;> simp [rcbσ, rcbW, rcbR]
  rw [maddJ_eq] at hR ⊢
  refine WP.mono (fprog_ok hL.lay hp _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun t ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, _, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx
  · exact (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 7) (ofN_run maddJN_ok hA E 8))).trans (maddJN_run _)

/-! ## The point -/

/-- An iteration's result with the mixed addition: `R` for a zero digit, else
`T` where `R = O`, else the mixed sum, a triple of a point of the curve,
`[winE k' J i]P` for `k < n`. -/
theorem jstepA_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 = 1) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (maddJF X1 Y1 Z1 X2 Y2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (maddJF X1 Y1 Z1 X2 Y2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (maddJF X1 Y1 Z1 X2 Y2).2.2) Q := by
  have hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  have noexc : k < C.n → 1 ≤ Window5.winE (k + 16 * Window5.geom J) J (i + 1) →
      mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P ≠
        Window5.winPt C P (k + 16 * Window5.geom J) i := fun hk he =>
    (Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he).1
  generalize k + 16 * Window5.geom J = k' at hadd h2 hQ1e noexc ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd hQ1e noexc
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    refine ⟨Q1, hQ1, fun hk => ?_, h1⟩
    rw [hQ1e hk, ← hadd, Window5.winPt_zero h0, add_infinity]
  simp only [h0, ↓reduceIte]
  obtain ⟨J2, z2⟩ := h2 (by omega_arith)
  subst z2
  have hW := Window5.onCurve_winPt hC hP k' i
  generalize hWe : Window5.winPt C P k' i = W at J2 hW hadd noexc ⊢
  cases W with
  | infinity => exact absurd ((J2.z_zero_iff hC).mpr rfl) hC.one_ne_zero
  | affine x2 y2 =>
  obtain ⟨ex2, ey2⟩ := J2.affine_coords hC
  have ex2' : X2 = x2 := by rw [ex2]; grind
  have ey2' : Y2 = y2 := by rw [ey2]; grind
  subst ex2' ey2'
  by_cases hz : Z1 = 0
  · simp only [hz, ↓reduceIte]
    refine ⟨_, hW, fun hk => ?_, J2⟩
    rw [← hadd, ← hQ1e hk, (h1.z_zero_iff hC).mp hz, infinity_add']
  simp only [hz, ↓reduceIte]
  by_cases hQW : Q1 = .affine X2 Y2
  · have hZ : (maddJF X1 Y1 Z1 X2 Y2).2.2 = 0 := by
      rw [hQW] at h1
      obtain ⟨hx1, -⟩ := h1.affine_coords hC
      rw [maddJF_z, hx1]; grind
    refine ⟨.infinity, rfl, fun hk => ?_, Or.inl ⟨rfl, hZ⟩⟩
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exact absurd ((h1.z_zero_iff hC).mpr (by rw [hQ1e hk, Nat.mul_zero, Window5.mul_zero_pt])) hz
      · exact h
    exact absurd (by rw [← hQ1e hk]; exact hQW) (noexc hk he1)
  · refine ⟨_, hC.onCurve_add hQ1 hW, fun hk => by rw [← hadd, hQ1e hk], ?_⟩
    exact h1.madd hC hM3 hQ1 hW hz hQW

/-! ## An iteration -/

/-- The loop's invariant: `JInv`, with the table's `Z` one. -/
def JInvA (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s : State) : Prop :=
  JInv K C base size P s₀ k j s ∧ JTblOne K base s

theorem JTblOne.loopW (hL : JacWinLay K size) {base : Addr} {s s' : State} (h : JTblOne K base s)
    (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) : JTblOne K base s' :=
  fun m h1 h16 => by
    rw [jgWord_unch hL hU hn (by omega_arith) (loopW_apart hL (by omega_arith))]
    exact h m h1 h16

/-- An iteration, `1 ≤ j ≤ J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstepA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j ≤ K.J) {s : State} (hI : JInvA K C base size P s₀ k j s) :
    WP isa (K.stepA dbl).inline s fun s' => JInvA K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨hI, hO1⟩ := hI
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  rw [JacWinCfg.stepA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have O₂ : JTblOne K base s₂ := (show JTblOne K base s₁ from fun m h1 h16 => by
    rw [m₁]; exact hO1 m h1 h16).loopW hL U₂ hn
  refine WP.seq (WP.mono (jentry_ok hL hF (j := j - 1) (by omega_arith) R₂.fr R₂.tbl b₂) fun s₃ h₃ =>
    WP.seq (WP.mono h₃ fun s₄ E₄ => ?_))
  -- `R` is not written by the entry.
  have hRe : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    have hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    refine E₄.unch.wordsVal (fun w hw => ?_) (by have := hL.le (other_mem hxo); omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.lay.tmp x (other_mem hxo)
  have U₄ : Unch base (jwLoopW K) s₂.mem s₄.mem := E₄.unch.mono (jent_loopW K)
  -- `T`'s `Z` is one.
  have tz1 : 1 ≤ magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1)) →
      tmv C K.M.n base s₄ K.E.z = 1 := fun h => by
    have hm : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1)) ≤ 16 :=
      magH_le (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) (j - 1); omega_arith)
    show toM _ _ _ = 1
    rw [← tz, E₄.zent h, O₂ _ h hm, hone]
  -- `D = R + T`.
  have V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.lt 1 (by decide)⟩
  have I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y]
      (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (madd_ok hL hp I₄ (fun x hx => hx)) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  have U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  have F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  -- `R` and `T` survive the addition.
  have keep₅ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n := by
    intro x hx
    have hxs : x ∈ jwSlots K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · jw_mem
      · jw_mem
      · jw_mem
      · exact mx
      · exact my
      · exact mz
    refine (ProgKeep.unch k₅).wordsVal (fun w hw => ?_) (by have := hL.le hxs; omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      exact cadd_apart hL x hx y hy
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp x hxs
  refine WP.mono (jmask_ok hL hF (i := j - 1) (by omega_arith) F₅ hb₅) fun s₆ ⟨F₆, U₆, b₆, z₆, w₆⟩ => ?_
  rw [offset_eq] at w₆
  have ent := E₄.ent
  rw [offset_eq] at ent tz1
  have R5 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base x K.M.n :=
    fun x hx => by
      rw [keep₅ x (List.mem_append_left [K.E.x, K.E.y, K.E.z] hx), hRe x hx]
  have T5 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n :=
    fun x hx => keep₅ x (List.mem_append_right [K.R.x, K.R.y, K.R.z] hx)
  have hz : wordsVal s₅.mem base K.R.z K.M.n = 0 ↔ tmv C K.M.n base s₂ K.R.z = 0 := by
    rw [R5 _ (by simp)]; exact (toM_eq_zero_iff hp (R₂.lt _ (by simp))).symm
  have Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base s₅ x = E₅ x ∧
      wordsVal s₅.mem base x K.M.n < C.p := fun x hx =>
    ⟨I₅.val x (List.mem_append_left _ hx), I₅.lt x (List.mem_append_left _ hx)⟩
  have tvR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₂ x := fun x hx => by rw [R5 x hx]
  have tvT : ∀ x ∈ [K.E.x, K.E.y, K.E.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₄ x := fun x hx => by rw [T5 x hx]
  have tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  have ex : tmv C K.M.n base s₆ K.R.x =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.x
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.x else E₅ K.D.x := by
    have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.x (by simp)) (tvT K.E.x (by simp)) (Dv K.D.x (by simp)).1
  have ey : tmv C K.M.n base s₆ K.R.y =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.y
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.y else E₅ K.D.y := by
    have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.y (by simp)) (tvT K.E.y (by simp)) (Dv K.D.y (by simp)).1
  have ez : tmv C K.M.n base s₆ K.R.z =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.z
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.z else E₅ K.D.z := by
    have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.z (by simp)) (tvT K.E.z (by simp)) (Dv K.D.z (by simp)).1
  have vx := congrArg Prod.fst v₅
  have vy := congrArg (fun p => p.2.1) v₅
  have vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  rw [vx] at ex; rw [vy] at ey; rw [vz] at ez
  have hR := jstepA_pt hC hM3 hO hP hP0 hn17 hn64 (k := k) (i := j - 1) (J := K.J) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (fun h => by
      have J := ent h
      have j1 := J.jac
      rw [tx, ty, tz] at j1
      exact ⟨j1, tz1 h⟩)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  have U₂₆ : Unch base (jwLoopW K) s₂.mem s₆.mem :=
    ((U₄.trans U₅).trans U₆).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with (hw | hw) | hw <;> exact hw
  refine ⟨⟨⟨⟨Q', hQ', hQe', F₆, ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL U₆ hn
    (by decide), fun x hx => ?_, ?_⟩, b₆⟩, O₂.loopW hL U₂₆ hn⟩, z₆⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp), ← tz]; exact E₄.lt 2 (by decide)
        · exact (Dv _ (by simp)).2
  · rw [ex, ey, ez]
    exact hR

/-! ## The window method -/

/-- What the method reads at the start survives what the table's building
and normalization write. -/
theorem JacWinFixed.unchA (hL : JacWinLay K size) {base : Addr} {s s' : State} {P : Point C} {k : Nat}
    {inv : Prog isa} {IW : List (Nat × Nat)} (hI : InvSpecJ K C base size inv IW)
    (hF : JacWinFixed K C base s P k) (hU : Unch base (jwW K ++ IW) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : JacWinFixed K C base s' P k := by
  have ro : ∀ x ∈ jwRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · rw [hL.Tx]; exact hL.jg_apart (List.mem_append_left _ hx) (by decide)
        · exact hL.lay.tmp x (ro_mem hx)
        · exact h x (ro_mem hx)) (by have := hL.le (ro_mem hx); omega_arith)
  have tv : ∀ x ∈ jwRo K, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => tmv_congr (ro x hx)
  refine ⟨by rw [ro _ (by jw_mem)]; exact hF.zero, fun x hx => ?_, ?_, ?_, fun t ht => ?_⟩
  · have hx' : x ∈ jwRo K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jw_mem
    rw [ro x hx']; exact hF.ro_lt x hx
  · rw [tv _ (by jw_mem), tv _ (by jw_mem), tv _ (by jw_mem)]; exact hF.pt
  · rw [tv _ (by jw_mem)]; exact hF.pz
  · have hb := hL.bits
    rw [hU.byte (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · have := hL.bits_w w hw; omega_arith
      · have := hI.bits w hw; omega_arith) (by omega_arith)]
    exact hF.bits t ht

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`, by the window method with
the table made affine, `inv` leaving `R.z^(p-2)` in `E.x`; only `invClob`,
`jwW` and what `inv` writes change. -/
theorem winJacA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr}
    (hI : InvSpecJ K C base size inv IW) {s₀ : State}
    (hs₀ : Scr s₀ base size) (hM₀ : ModOkW K.M size C.p s₀.mem base) (hF₀ : JacWinFixed K C base s₀ P k) :
    WP isa (K.windowA inv dbl).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (jwW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs₀.nowrap
  have hJ := hL.J
  have hP0 : P ≠ .infinity := by
    intro h
    have := hF₀.pt
    rw [h, hF₀.pz] at this
    exact hC.one_ne_zero this.2.2
  have pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [JacWinCfg.windowA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs₀ hM₀ hF₀) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (normA_ok hL hp hC hpn hone_lt hone hI F₁.scr F₁.mod T₁)
    fun s ⟨hs, Kn, Un, hM, T₂, O₂⟩ => ?_)
  have U₀ : Unch base (jwW K ++ IW) s₀.mem s.mem := (F₁.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  have hF : JacWinFixed K C base s P k := hF₀.unchA hL hI U₀ hn
  have K₀ : KeepRegs (invClob K.M.n) s₀ s := (F₁.keep.mono pc).trans Kn
  refine WP.seq (WP.mono (jfirst_ok hL hC hP hF hkJ (JFrame.refl hs hM) T₂) fun s₂ ⟨I₂, U₂⟩ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvA K C base size P s k 0 t)
    (Inv := fun j t => JInvA K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstepA_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hone hF h1 (by omega_arith) hi)
    (fun _ h => h) (by omega_arith) ⟨I₂, O₂.loopW hL U₂ hn⟩) fun s₃ ⟨I₃, _⟩ => ?_)
  obtain ⟨Q, -, hQe, R₃⟩ := I₃.st
  rw [Window5.winE_zero'] at hQe
  -- `Y = 1` where `Z = 0`.
  have hs₃ := R₃.fr.scr
  have hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [R₃.fr.ro hL (by jw_mem)]; exact hF.zero
  have ayz : K.R.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.R.y :=
    hL.ap (by jw_mem) (by jw_mem) (fun e => hL.ro K.zero (by jw_mem) (by rw [← e]; jw_mem))
  refine WP.seq (WP.mono (outFix_ok K.tc hs₃ hL.n0 (Nat.lt_trans hone_lt hpn)
    (show K.R.y + 8 * K.M.n ≤ size from hL.le (by jw_mem)) (show K.R.z + 8 * K.M.n ≤ size from hL.le (by jw_mem))
    (show K.zero + 8 * K.M.n ≤ size from hL.le (by jw_mem)) ayz hz₃) fun s₄ ⟨ey₄', k₄, O₄'⟩ => ?_)
  have ey₄ : wordsVal s₄.mem base K.R.y K.M.n = if wordsVal s₃.mem base K.R.z K.M.n = 0 then K.one
      else wordsVal s₃.mem base K.R.y K.M.n := ey₄'
  have O₄ : Outside base K.R.y (8 * K.M.n) s₃.mem s₄.mem := O₄'
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  have ex₄ : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₃.mem base K.R.x K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  have ez₄ : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₃.mem base K.R.z K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 2) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  have U₄ : Unch base (jwLoopW K) s₃.mem s₄.mem := O₄.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw]; exact other_loopW (by jw_mem)
  have F₄ := R₃.fr.next hL hs₄ (k₄.mono (sub_powClob (by decide))) U₄ (jwLoopW_sub K)
  have hlt₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₄]; exact R₃.lt _ (by simp)
    · rw [ey₄]; split
      · exact hone_lt
      · exact R₃.lt _ (by simp)
    · rw [ez₄]; exact R₃.lt _ (by simp)
  have hSlR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s₄) s₄ :=
    ⟨hs₄, F₄.mod, hSlR, hlt₄, fun _ _ => rfl⟩
  have hS : ∀ op ∈ K.tc.outOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> jw_mem
  have hR : readsOk K.tc.outOps [K.R.x, K.R.y, K.R.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out, JacWinCfg.tc]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ I₄ hS hR) fun s₅ ⟨P₅, I₅⟩ => ?_
  have hval : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      runOps K.tc.outOps (tmv C K.M.n base s₄) x ∧ wordsVal s₅.mem base x K.M.n < C.p := fun x hx => by
    have hm : x ∈ validAfter K.tc.outOps [K.R.x, K.R.y, K.R.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  have U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := P₅.loopW (by
    intro x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, FOp.out, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem))
  have F₅ := F₄.next hL (P₅.scr hs₄) P₅.regs U₅ (jwLoopW_sub K)
  refine ⟨K₀.trans (F₅.keep.mono pc), (U₀.trans F₅.unch).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
    F₅.mod, fun x hx => (hval x hx).2, fun hk => ?_⟩
  have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₅ x = runOps K.tc.outOps (tmv C K.M.n base s₄) x :=
    fun x hx => (hval x hx).1
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  have hxt : K.R.x ≠ K.S.t0 := hL.oth_ne (i := 0) (j := 7) (by decide) (by decide) (by decide)
  have hzt : K.R.z ≠ K.S.t0 := hL.oth_ne (i := 2) (j := 7) (by decide) (by decide) (by decide)
  have hxz : K.R.x ≠ K.R.z := hL.oth_ne (i := 0) (j := 2) (by decide) (by decide) (by decide)
  have hxy : K.R.x ≠ K.R.y := hL.oth_ne (i := 0) (j := 1) (by decide) (by decide) (by decide)
  have hyt : K.R.y ≠ K.S.t0 := hL.oth_ne (i := 1) (j := 7) (by decide) (by decide) (by decide)
  have hyz : K.R.y ≠ K.R.z := hL.oth_ne (i := 1) (j := 2) (by decide) (by decide) (by decide)
  simp only [TCombCfg.outOps, JacWinCfg.tc, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply, hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
  have hy : tmv C K.M.n base s₄ K.R.y = if tmv C K.M.n base s₃ K.R.z = 0 then 1
      else tmv C K.M.n base s₃ K.R.y := by
    show toM _ _ _ = _
    rw [ey₄]
    by_cases h : wordsVal s₃.mem base K.R.z K.M.n = 0
    · have h' : tmv C K.M.n base s₃ K.R.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
      simp only [h, h', ↓reduceIte]; exact hone
    · have h' : tmv C K.M.n base s₃ K.R.z ≠ 0 := fun h0 =>
        h ((toM_eq_zero_iff hp (R₃.lt _ (by simp))).mp h0)
      simp only [h, h', ↓reduceIte]
  have ex : tmv C K.M.n base s₄ K.R.x = tmv C K.M.n base s₃ K.R.x := by
    show toM _ _ _ = toM _ _ _; rw [ex₄]
  have ez : tmv C K.M.n base s₄ K.R.z = tmv C K.M.n base s₃ K.R.z := by
    show toM _ _ _ = toM _ _ _; rw [ez₄]
  rw [hy, ex, ez, ← hQe hk]
  exact InvJ.out hC R₃.rep

end VG.Proof.Weierstrass.X86_64
