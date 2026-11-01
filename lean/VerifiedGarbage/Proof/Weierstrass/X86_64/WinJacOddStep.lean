module

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOps
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacIP
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.OddWin
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay

/-!
# The odd window method on x86-64: an iteration

`JacWinCfg.stepO`: `rbx = j - 1`, `R = 32 R` (`dblsO_ok`), digit `j - 1`'s
entry in `T` (`jentryO_ok`), and `R = R + T` in place (`caddO_ok`): `R` then
represents `[S_{j-1}]P` for an odd `k < n` (`jstepO_point`), as no addition
is exceptional (`OddWin.loop_noexc`), and some point of the curve for any
`k` (`jstepO_pt`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The addition in place -/

/-- What `R = R + T` writes and reads are apart as `ipσ` numbers them. -/
theorem JacWinLay.ipApart (hL : JacWinLay K size) : CachedJac.IPApart K.M.n K.S K.R K.E K.z2 := by
  have hgW : ∀ c < 5, jg K (80 + c) ∉ rcbW K.S K.R := by
    intro c hc hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have g := fun x (hx : x ∈ jwOther K) => hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega)
    rcases hw with h | h | h | h | h | h | h | h | h <;> exact g _ (by jw_mem) h.symm
  refine ⟨hL.rcbW_R, fun x hx => ?_⟩
  simp only [CachedJac.ipR, List.mem_cons, List.not_mem_nil, or_false] at hx
  show x ∉ rcbW K.S K.R
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro hw
    exact hL.ro K.S.a (by jw_mem) (by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
  · intro hw
    exact hL.ro K.S.b3 (by jw_mem) (by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
  · rw [hL.Tx]; exact hgW 0 (by decide)
  · rw [hL.Ty]; exact hgW 1 (by decide)
  · rw [hL.Tz]; exact hgW 2 (by decide)
  · rw [hL.Tz2]; exact hgW 3 (by decide)
  · rw [hL.Tz3]; exact hgW 4 (by decide)

/-- `R = R + T` in place, with `T`'s cached `Z²` and `Z³`. -/
theorem caddO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], x ∈ V)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z) :
    WP isa (ForwardField.programB K.M K.addOpsO).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.R) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E' t ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) =
          jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hA := hL.ipApart
  have hSl : ∀ x ∈ CachedJac.ipW K.S K.R ++ CachedJac.ipR K.M.n K.S K.E K.z2, x ∈ jwSlots K := by
    intro x hx
    simp only [CachedJac.ipW, CachedJac.ipR, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hr : readsOk K.addOpsO V = true := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    refine readsOk_mono (readsOk_rename (CachedJac.ipσ K.M.n K.S K.R K.E K.z2)
      (show readsOk (CachedJac.headIPN ++ CachedJac.tailIPN) [6, 7, 8, 11, 12, 13, 14, 15] = true by decide))
      fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp [CachedJac.ipσ, CachedJac.ipW, CachedJac.ipR]
  have hs : ∀ op ∈ K.addOpsO, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    intro op hop x hx
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    refine hSl x ?_
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] at hx <;> rcases hx with rfl | rfl | rfl <;> exact CachedJac.ipσ_mem ..
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hs hr) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, _, it.sub fun x hx => ?_, CachedJac.ip_run hA E h2 h3⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq] at hop
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact CachedJac.ipσ_out _ _ _ _ _ (CachedJac.ipN_out op' hop')
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOpsO, jacTail, FOp.out]
    · exact Or.inl hx

/-! ## The point -/

/-- The iteration's sum for an odd `k < n`: a triple of `[S_i]P`. -/
theorem jstepO_point (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {k J i : Nat}
    (hk : k % 2 = 1) (hkn : k < C.n) (hi : i + 1 < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul (32 * OddWin.oS J k (i + 1)) P))
    (h2 : InvJ C X2 Y2 Z2 (OddWin.oddPt C P J k i)) (z2 : Z2 ≠ 0) :
    InvJ C (jacAddF X1 Y1 Z1 X2 Y2 Z2).1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2
      (mul (OddWin.oS J k i) P) := by
  obtain ⟨ne0, ne1, ne2⟩ := OddWin.loop_noexc hC hO hP hP0 hn2 hn64 hnb hk hkn hi
  rw [← OddWin.win_add hC hP hk (by omega)]
  have hQ := hC.onCurve_mul hP (32 * OddWin.oS J k (i + 1))
  have hW := OddWin.onCurve_oddPt hC hP J k i
  have hz : Z1 ≠ 0 := fun h => ne0 ((h1.z_zero_iff hC).mp h)
  have hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
    intro hx
    by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
    · exact ne1 (h1.same hC h2 hz z2 hx hy)
    · exact ne2 (h1.opposite hC hQ hW h2 hz z2 hx hy)
  exact h1.add_ne hC hM3 hQ hW h2 hz z2 hh

/-- The iteration's sum for any `k`: a triple of a point of the curve, which
is `[S_i]P` for an odd `k < n` (`jstepO_point`). Beyond it an addition may
be exceptional or start from `O`: then `Z = 0`, a triple of `O`. -/
theorem jstepO_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {k J i : Nat}
    (hi : i + 1 < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k % 2 = 1 ∧ k < C.n → Q1 = mul (32 * OddWin.oS J k (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1) (h2 : InvJ C X2 Y2 Z2 (OddWin.oddPt C P J k i)) (z2 : Z2 ≠ 0) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS J k i) P) ∧
      InvJ C (jacAddF X1 Y1 Z1 X2 Y2 Z2).1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1
        (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2 Q := by
  by_cases hk : k % 2 = 1 ∧ k < C.n
  · refine ⟨_, hC.onCurve_mul hP _, fun _ => rfl, ?_⟩
    rw [hQ1e hk] at h1
    exact jstepO_point hC hM3 hO hP hP0 hn2 hn64 hnb hk.1 hk.2 hi h1 h2 z2
  have nk : ∀ Q : Point C, k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS J k i) P := fun _ h' => absurd h' hk
  have hW := OddWin.onCurve_oddPt hC hP J k i
  have zO : (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2 = Z1 * Z2 * (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) := rfl
  by_cases hz : Z1 = 0
  · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
    rw [zO, hz]; grind
  · by_cases hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) = 0
    · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
      rw [zO, hh]; grind
    · exact ⟨_, hC.onCurve_add hQ1 hW, nk _, h1.add_ne hC hM3 hQ1 hW h2 hz z2 hh⟩

end VG.Proof.Weierstrass.X86_64
