module
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block

/-!
# The Jacobian window method on x86-64: the masks of an iteration

`D = T` where `R = O`, and `R = D` unless the digit is zero (`jmask_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The point -/

/-! ## The masks -/

/-- `D = T` where `R`'s `Z` is zero, and `R = D` unless digit `i` is zero. -/
theorem jmask_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {s : State} {i : Nat} (hi : i < K.J)
    (hf : JFrame K C base size s₀ s) (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    WP isa (.block (nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++ K.tc.digit ++ eqMask 0 ++
      selPt K.M.n K.R K.D K.R ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))) s fun t =>
      JFrame K C base size s₀ t ∧ Unch base (jwLoopW K) s.mem t.mem ∧ t.gpr .rbx = BitVec.ofNat 64 i ∧
      t.zf = some (decide (i = 0)) ∧
      ∀ c < 3, wordsVal t.mem base ([K.R.x, K.R.y, K.R.z].getD c 0) K.M.n =
        if magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 then
          wordsVal s.mem base ([K.R.x, K.R.y, K.R.z].getD c 0) K.M.n
        else if wordsVal s.mem base K.R.z K.M.n = 0 then
          wordsVal s.mem base ([K.E.x, K.E.y, K.E.z].getD c 0) K.M.n
        else wordsVal s.mem base ([K.D.x, K.D.y, K.D.z].getD c 0) K.M.n := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hnn := hL.n0
  have hbl := hL.bits
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have ap := fun {x y : Nat} (hx : x ∈ jwSlots K) (hy : y ∈ jwSlots K) (h : x ≠ y) => hL.ap hx hy h
  have hDE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], ∀ y ∈ [K.E.x, K.E.y, K.E.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    have hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact hL.jg_apart (List.mem_append_right _ hxo) (by decide)
  have hRD : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact hL.ap_oth (i := 0) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 0) (j := 5) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 1) (j := 5) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 3) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 4) (by decide) (by decide) (by decide)
      | exact hL.ap_oth (i := 2) (j := 5) (by decide) (by decide) (by decide)
  have dd := And.intro (hL.ap_oth (i := 3) (j := 4) (by decide) (by decide) (by decide))
    (And.intro (hL.ap_oth (i := 3) (j := 5) (by decide) (by decide) (by decide))
      (hL.ap_oth (i := 4) (j := 5) (by decide) (by decide) (by decide)))
  have rr := And.intro (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide))
    (And.intro (hL.ap_oth (i := 0) (j := 2) (by decide) (by decide) (by decide))
      (hL.ap_oth (i := 1) (j := 2) (by decide) (by decide) (by decide)))
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hL.le (by jw_mem)
  have leE : ∀ x ∈ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z], x + 8 * K.M.n ≤ size := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.le (by jw_mem)
    · exact hL.le (by jw_mem)
    · exact hL.le (by jw_mem)
    · exact hL.le mx
    · exact hL.le my
    · exact hL.le mz
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hnn (hL.le (by jw_mem : K.R.z ∈ jwSlots K))) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₁ (decide (wordsVal s.mem base K.R.z K.M.n ≠ 0)) (by rw [c₁])
    (o := K.D) (a := K.E) leE dd hDE) fun s₂ ⟨dx, dy, dz, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at dx dy dz O₂
  have UD : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s.mem s₂.mem :=
    fun x hx => O₂ x (hx (K.D.x, 8 * K.M.n) (by simp)) (hx (K.D.y, 8 * K.M.n) (by simp))
      (hx (K.D.z, 8 * K.M.n) (by simp))
  have F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) UD (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact mem_jwW_ws (other_ws (by jw_mem)))
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 i := by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hb]
  rw [WP.block_append_iff]
  have hwj : 5 * i + 5 ≤ 5 * K.J := by omega_arith
  have hbits₂ := F₂.bits hL hF
  refine WP.mono (digit_ok K.tc hs₂ (N := 5 * K.J) (by show 1 ≤ 5; decide) (by show 5 < 9; decide) hwj
    (by show K.bits + 5 * K.J ≤ size; omega_arith) hb₂ hbits₂) fun s₃ ⟨_, r₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [show K.tc.w = 5 from rfl, Window5.combWin_five, show K.tc.H = 16 from rfl] at r₃
  have hm := magH_le (H := 16) (v := Window5.nib (k + JacWinCfg.offset K.J) i)
    (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) i; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₃ (v := 0) (by decide) (by omega_arith) r₃) fun s₄ ⟨c₄, k₄, _⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₄ (decide (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0))
    (by rw [c₄]) (o := K.R) (a := K.D) le rr hRD) fun s₅ ⟨rx, ry, rz, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₂.mem := by rw [k₄.2.1, k₃.2.1]
  rw [m₄] at rx ry rz O₅
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 i := by
    rw [k₅.gpr _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), hb₂]
  refine WP.mono (testRbx_ok s₅ (by omega_arith) hb₅) fun t ⟨z₆, k₆⟩ => ?_
  have m₆ : t.mem = s₅.mem := k₆.2.1
  have UR : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₂.mem t.mem := by
    rw [m₆]; exact fun x hx => O₅ x (hx (K.R.x, 8 * K.M.n) (by simp)) (hx (K.R.y, 8 * K.M.n) (by simp))
      (hx (K.R.z, 8 * K.M.n) (by simp))
  have F₆ := F₂.next hL (hs₅.of_keeps k₆ (by decide)) (((((Keeps.regs k₃).mono (sub_powClob (by decide))).trans
    ((Keeps.regs k₄).mono (sub_powClob (by decide)))).trans (k₅.mono (sub_powClob (by decide)))).trans
    ((Keeps.regs k₆).mono (by simp))) UR (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact mem_jwW_ws (other_ws (by jw_mem)))
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  -- `R` and `E` are not written by the first selection.
  have kR : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₂.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    refine UD.wordsVal (fun w hw => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hw' : w.1 ∈ [K.D.x, K.D.y, K.D.z] ∧ w.2 = 8 * K.M.n := by rcases hw with rfl | rfl | rfl <;> simp
      rw [hw'.2]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hRD _ (by simp) _ hw'.1
      · exact hRD _ (by simp) _ hw'.1
      · exact hRD _ (by simp) _ hw'.1
      · exact (hDE _ hw'.1 _ (by simp)).symm
      · exact (hDE _ hw'.1 _ (by simp)).symm
      · exact (hDE _ hw'.1 _ (by simp)).symm
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact b64 _ (by jw_mem)
      · exact b64 _ (by jw_mem)
      · exact b64 _ (by jw_mem)
      · exact b64 _ mx
      · exact b64 _ my
      · exact b64 _ mz
  refine ⟨F₆, (UD.trans UR).mono fun w hw => ?_, by rw [k₆.1 _ (by simp), hb₅], z₆, fun c hc => ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> exact other_loopW (by jw_mem)
  · have : c = 0 ∨ c = 1 ∨ c = 2 := by omega_arith
    rcases this with rfl | rfl | rfl
    · show wordsVal t.mem base K.R.x K.M.n = _
      rw [m₆, rx, dx, kR K.R.x (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]
    · show wordsVal t.mem base K.R.y K.M.n = _
      rw [m₆, ry, dy, kR K.R.y (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]
    · show wordsVal t.mem base K.R.z K.M.n = _
      rw [m₆, rz, dz, kR K.R.z (by simp)]
      by_cases h0 : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) i) = 0 <;>
        by_cases hz : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h0, hz]

end VG.Proof.Weierstrass.X86_64
