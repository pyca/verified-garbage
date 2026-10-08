import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter

/-!
# Scalar multiplication by 5-bit windows in Jacobian coordinates on x86-64

`JacWinCfg.window K dbl` (`Impl/Weierstrass/X86_64/WinJac.lean`) leaves `R`
representing `[k]P` in projective coordinates (`winJac_ok`), for `k < n` on a
curve of prime order `n ≡ 17 (mod 32)` (as P-256's), whose bits plus the
recoding's offset are the table at `K.bits`, with any doubling `dbl` that
doubles a Jacobian triple in place (`DblOk`): the table `[1 … 16]P` by co-Z
formulas (`jbuild_ok`), `R = [d_{J-1}]P` from the top digit (`jfirst_ok`),
`J - 1` iterations `R = 32 R + [d_j]P` (`jstep_ok`), whose additions are never
exceptional for `k < n` (`Window5.loop_noexc`), and `R = (XZ : Y : Z³)` with
`Y = 1` for `O`. For `k ≥ n` (whose result the callers do not use) the code
runs the same way and writes the same places, and `R` is a triple of some
point of the curve.
-/

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
  refine WP.mono (mov32Rbx_ok s (j := K.J - 1) (by omega)) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hf.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have F₁ := hf.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  have T₁ : JTblOk K C base P 16 s₁ := fun m h1 hm => (hT m h1 hm).congr fun c _ => by rw [m₁]
  rw [WP.block_append_iff]
  refine WP.mono (jentry_ok hL hF (j := K.J - 1) (by omega) F₁ T₁ b₁) fun s₂ h₂ => ?_
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
    (Nat.le_add_left _ _) (by omega)
  rw [show K.J - 1 + 1 = K.J by omega, Window5.winE_top hk', Nat.mul_zero, Window5.mul_zero_pt,
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
    · have J := (ent (by omega)).jac
      rw [tx, ty, tz] at J
      exact J
  · rw [k₄.gpr _ (by decide), E₃.keep.gpr _ (rbx_not_clob _), b₁]

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`; only `powClob` and `jwW`
change. -/
theorem winJac_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixed K C base s P k) :
    WP isa (K.window dbl) s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have hP0 : P ≠ .infinity := by
    intro h
    have := hF.pt
    rw [h, hF.pz] at this
    exact hC.one_ne_zero this.2.2
  rw [JacWinCfg.window]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega) hs hM hF) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirst_ok hL hC hP hF hkJ F₁ T₁) fun s₂ ⟨I₂, _⟩ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInv K C base size P s k 0 t)
    (Inv := fun j t => JInv K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstep_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hF h1 (by omega) hi)
    (fun _ h => h) (by omega) I₂) fun s₃ I₃ => ?_)
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
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega
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

end VG.Proof.Weierstrass.X86_64
