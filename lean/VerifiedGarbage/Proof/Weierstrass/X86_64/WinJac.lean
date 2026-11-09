module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block

/-!
# Scalar multiplication by 5-bit windows on x86-64: the top digit

`R = [d_{J-1}]P` from the top digit, and `rbx = J - 1` (`jfirst_ok`), as the
window method with an affine table (`WinJacA.lean`) starts, for a curve of
prime order `n ≡ 17 (mod 32)` (as P-256's) whose scalar's bits plus the
recoding's offset are the table at `K.bits`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The top digit's entry into `R`, and `rbx = J - 1`: `R` is a triple of
`[d_{J-1}]P = [winE k' J (J - 1)]P`, or zeros for the digit zero. -/
theorem jfirst_ok (hL : JacWinLay K size) (hC : Law C) {base : Addr} {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k)
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) :
    WP isa (.block K.first) s fun t => JInv K C base size P s₀ k (K.J - 1) t ∧
      Unch base (jwLoopW K) s.mem t.mem := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  rw [show K.first = [.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))] ++
      ((K.tc.digit ++ K.select) ++ (K.tc.negY ++ copyPt K.M.n K.R K.E)) by
    simp only [JacWinCfg.first, List.append_assoc], WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s (j := K.J - 1) (by omega_arith)) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hf.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have F₁ := hf.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  have T₁ : JTblOk K C base P 16 s₁ := fun m h1 hm => (hT m h1 hm).congr fun c _ => by rw [m₁]
  rw [WP.block_append_iff]
  refine WP.mono (jentry_ok hL hF (j := K.J - 1) (by omega_arith) F₁ T₁ b₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₂ fun s₃ E₃ => ?_
  -- `R = T`.
  have hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have hRE : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact other_mem (by jw_mem)
    · exact other_mem (by jw_mem)
    · exact other_mem (by jw_mem)
    · exact mx
    · exact my
    · exact mz
  have hne : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.E.x, K.E.y, K.E.z] := by
    intro x hx hy
    simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h <;>
      exact hL.jg_ne (List.mem_append_right _ (hR x hx)) (by decide) h
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  refine WP.mono (copyPt_ok E₃.fr.scr (n := K.M.n) (o := K.R) (a := K.E) (fun x hx => hL.le (hRE x hx))
    (fun x hx y hy hxy => hL.ap (hRE x (List.mem_append_left [K.E.x, K.E.y, K.E.z] hx)) (hRE y hy) hxy) hne
    ⟨o 0 1 (by decide) (by decide) (by decide), o 0 2 (by decide) (by decide) (by decide),
      o 1 2 (by decide) (by decide) (by decide)⟩) fun s₄ ⟨ex, ey, ez, k₄, U₄⟩ => ?_
  have hs₄ := E₃.fr.scr.of_keepRegs k₄ (by decide)
  have UL : Unch base (jwLoopW K) s₃.mem s₄.mem := U₄.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact other_loopW (hR _ (by simp))
  have F₄ := E₃.fr.next hL hs₄ (k₄.mono (sub_powClob (by decide))) UL (jwLoopW_sub K)
  -- The point.
  have hk' : k + 16 * Window5.geom K.J < 32 ^ K.J := by rw [← offset_eq]; exact hkJ
  have hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom K.J) (J := K.J) (j := K.J - 1)
    (Nat.le_add_left _ _) (by omega_arith)
  rw [show K.J - 1 + 1 = K.J by omega_arith, Window5.winE_top hk', Nat.mul_zero, Window5.mul_zero_pt,
    infinity_add'] at hadd
  have ent := E₃.ent
  have zer := E₃.zero
  rw [offset_eq] at ent zer
  have tv : ∀ {x y : Nat}, wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base y K.M.n →
      tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  refine ⟨⟨⟨Window5.winPt C P (k + 16 * Window5.geom K.J) (K.J - 1), Window5.onCurve_winPt hC hP _ _,
    fun _ => hadd, F₄, (T₁.loopW hL (E₃.unch.mono (jent_loopW K)) hn (by decide)).loopW hL UL hn (by decide),
    fun x hx => ?_, ?_⟩, ?_⟩, by
      rw [← m₁]; exact ((E₃.unch.mono (jent_loopW K)).trans UL).mono fun w hw => (List.mem_append.mp hw).elim id id⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex, ← tx]; exact E₃.lt 0 (by decide)
    · rw [ey, ← ty]; exact E₃.lt 1 (by decide)
    · rw [ez, ← tz]; exact E₃.lt 2 (by decide)
  · rw [tv ex, tv ey, tv ez]
    by_cases h0 : magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (K.J - 1)) = 0
    · rw [Window5.winPt_zero h0]
      exact Or.inl ⟨rfl, by rw [← tz]; exact zer h0⟩
    · have J := (ent (by omega_arith)).jac
      rw [tx, ty, tz] at J
      exact J
  · rw [k₄.gpr _ (by decide), E₃.keep.gpr _ (rbx_not_clob _), b₁]

end VG.Proof.Weierstrass.X86_64
