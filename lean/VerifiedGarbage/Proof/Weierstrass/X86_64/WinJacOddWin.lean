module

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddBuild
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddEntry
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.OddWin
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState

/-!
# Scalar multiplication by odd 5-bit windows in Jacobian coordinates on x86-64

`JacWinCfg.windowO K dbl` (`Impl/Weierstrass/X86_64/WinJacOdd.lean`) leaves
`R` representing `[k]P` in projective coordinates (`winJacO_ok`), for an odd
`k < n`, `k ≤ 2 · 32^(J-1)`, on a curve of prime order `n` with
`n mod 64 < 33` (as P-256's), whose table at `K.bits` holds the bits of
`oq J k`, with any doubling `dbl` that doubles a Jacobian triple in place
(`DblOk`): the table `[1]P, [3]P, …, [31]P` (`jbuildO_ok`), `R = P` for the
top digit 1 (`jfirstO_ok`), and `J - 1` iterations `R = 32 R + [d_j]P`
(`jstepO_ok`), whose additions are never exceptional (`OddWin.loop_noexc`),
then `R = (XZ : Y : Z³)` with `Y = 1` for `O`. For any other `k` the code
runs the same way and writes the same places, and `R` is a triple of some
point of the curve.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The odd loop's invariant at `rbx = j`: `R` is a triple of a point of the
curve, `[S_j]P` for an odd `k < n`. -/
structure JInvO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  st : ∃ Q : Point C, onCurve C Q = true ∧
    (k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS K.J k j) P) ∧ RStO K C base size P s₀ Q s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j

/-- An iteration, `1 ≤ j < J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstepO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j < K.J) {s : State} (hI : JInvO K C base size P s₀ k j s) :
    WP isa (K.stepO dbl).inline s fun s' => JInvO K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  rw [JacWinCfg.stepO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, _⟩ => ?_)
  refine WP.seq (WP.mono (jentryO_ok hL hF (j := j - 1) (by omega_arith) R₂.fr R₂.tbl b₂) fun s₃ h₃ =>
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
  -- `R = R + T`.
  have V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.ent.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.ent.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact E₄.ent.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact E₄.ent.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact E₄.ent.lt 4 (by decide)⟩
  have I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  have h2 := E₄.ent.z2; have h3 := E₄.ent.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  refine WP.seq (WP.mono (caddO_ok hL hp I₄ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  have U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  have F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  refine WP.mono (testRbx_ok s₅ (by omega_arith) hb₅) fun s₆ ⟨z₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  have F₆ := F₅.next hL (F₅.scr.of_keeps k₆ (by decide)) ((Keeps.regs k₆).mono (by simp)) (W := [])
    (by rw [m₆]; exact Unch.refl _ _ _) (by simp)
  have tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  have Rv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₆ x = E₅ x ∧
      wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
    have hm : x ∈ [K.R.x, K.R.y, K.R.z] ++ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
        K.z2 + 8 * K.M.n] := List.mem_append_left _ hx
    exact ⟨by show toM _ _ _ = _; rw [m₆]; exact I₅.val x hm, by rw [m₆]; exact I₅.lt x hm⟩
  have hR := jstepO_pt hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := j - 1) (J := K.J) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (by have J := E₄.ent.jac; rw [tx, ty, tz] at J; exact J) (by have J := E₄.ent.z; rw [tz] at J; exact J)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  have vx := congrArg Prod.fst v₅
  have vy := congrArg (fun p => p.2.1) v₅
  have vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  refine ⟨⟨⟨Q', hQ', hQe', F₆,
    ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL
      (by rw [m₆]; exact Unch.refl _ _ _) hn (by decide),
    fun x hx => (Rv x hx).2, ?_⟩, by rw [k₆.1 _ (by simp), hb₅]⟩, z₆⟩
  rw [(Rv _ (by simp)).1, (Rv _ (by simp)).1, (Rv _ (by simp)).1, vx, vy, vz]
  exact hR

/-- `rbx = J - 1` and `R = P`: a triple of `[S_{J-1}]P = [1]P`. -/
theorem jfirstO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} (hP : onCurve C P = true)
    {s₀ s : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) (hJ1 : 1 ≤ K.J)
    (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) :
    WP isa (.block K.firstO) s fun t => JInvO K C base size P s₀ k (K.J - 1) t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [JacWinCfg.firstO, WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s (j := K.J - 1) (by omega_arith)) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hf.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have F₁ := hf.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  have hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have hPro : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have hRP : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.R.x, K.R.y, K.R.z] ++ [K.P.x, K.P.y, K.P.z] by simpa using hx)
      with hx | hx
    · exact other_mem (hR x hx)
    · exact ro_mem (hPro x hx)
  have hne : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.P.x, K.P.y, K.P.z] := fun x hx hy =>
    hL.ro x (hPro x hy) (List.mem_append_left _ (hR x hx))
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  refine WP.mono (copyPt_ok hs₁ (n := K.M.n) (o := K.R) (a := K.P) (fun x hx => hL.le (hRP x hx))
    (fun x hx y hy hxy => hL.ap (hRP x (List.mem_append_left [K.P.x, K.P.y, K.P.z] hx)) (hRP y hy) hxy) hne
    ⟨o 0 1 (by decide) (by decide) (by decide), o 0 2 (by decide) (by decide) (by decide),
      o 1 2 (by decide) (by decide) (by decide)⟩) fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have UL : Unch base (jwLoopW K) s₁.mem s₂.mem := U₂.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact other_loopW (hR _ (by simp))
  have F₂ := F₁.next hL hs₂ (k₂.mono (sub_powClob (by decide))) UL (jwLoopW_sub K)
  have T₁ : JTblOkO K C base P 16 s₁ := fun m h1 hm => (hT m h1 hm).congr fun c _ => by rw [m₁]
  have tv : ∀ {x y : Nat}, wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base y K.M.n →
      tmv C K.M.n base s₂ x = tmv C K.M.n base s₁ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  have J₁ := hF.jac hL F₁
  have lt₁ := hF.lt hL F₁
  have hz : tmv C K.M.n base s₁ K.P.z = 1 := by rw [F₁.ro_tmv hL (by jw_mem)]; exact hF.pz
  refine ⟨⟨P, hP, fun hk => ?_, ⟨F₂, T₁.loopW hL UL hn (by decide), fun x hx => ?_, ?_⟩⟩,
    by rw [k₂.gpr _ (by decide), b₁]⟩
  · rw [(OddWin.oe_top hk.1 hJ1 hkJ).2, mul_one_pt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact lt₁ _ (by simp)
    · rw [ey]; exact lt₁ _ (by simp)
    · rw [ez]; exact lt₁ _ (by simp)
  · rw [tv ex, tv ey, tv ez, hz]; exact J₁

/-- The end of the window method, from `rbx = 0`: `R = (XZ : Y : Z³)` with
`Y = 1` for `O`, a triple of `[k]P` for an odd `k < n`. -/
theorem jfinO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {P : Point C} {k : Nat} {base : Addr} {s s₃ : State}
    (hF : JacWinFixedO K C base s P k) (I₃ : JInvO K C base size P s k 0 s₃) :
    WP isa (Code.seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps).inline) s₃ fun s' =>
      KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hJ := hL.J
  obtain ⟨Q, -, hQe', R₃⟩ := I₃.st
  have hQe : k % 2 = 1 ∧ k < C.n → Q = mul k P := fun hk => by
    rw [hQe' hk, OddWin.oS_zero hk.1 (by omega_arith)]
  -- `Y = 1` where `Z = 0`.
  have hs₃ := R₃.fr.scr
  have hn := hs₃.nowrap
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
  refine ⟨F₅.keep, F₅.unch, F₅.mod, fun x hx => (hval x hx).2, fun hk => ?_⟩
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


/-- `[k]P` into `R`, in projective coordinates, for `k` whose `oq J k` is the
table of bits at `K.bits`, if `k` is odd and below `n`; only `powClob` and
`jwW` change. -/
theorem winJacO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowO dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have hP0 := hF.ne_infinity hC
  rw [JacWinCfg.windowO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuildO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs hM hF.toJacWinPt)
    fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirstO_ok hL hP hF (by omega_arith) hkJ F₁ T₁) fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvO K C base size P s k 0 t)
    (Inv := fun j t => JInvO K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstepO_ok hL hp hC hM3 hO hD hP hP0 hn2 hn64 hnb hF h1 (by omega_arith) hi)
    (fun _ h => h) (by omega_arith) I₂) fun s₃ I₃ => ?_)
  exact jfinO_ok hL hp hC hpn hone_lt hone hF I₃

end VG.Proof.Weierstrass.X86_64
