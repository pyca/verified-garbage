import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter

/-!
# Scalar multiplication by 5-bit windows in Jacobian coordinates on x86-64

`JacWinCfg.window K dbl` (`Impl/Weierstrass/X86_64/WinJac.lean`) leaves `R`
representing `[k]P` in projective coordinates (`winJac_ok`), for `k < n` on a
curve of prime order `n ≡ 17 (mod 32)` (as P-256's), whose bits plus the
recoding's offset are the table at `K.bits`, with any doubling `dbl` that
doubles a Jacobian triple in place (`DblOk`): the table `[1 … 16]P`
(`build_ok`), `R = O` (`jinit_ok`), `J` iterations `R = 32 R + [d_j]P`
(`jstep_ok`), whose additions are never exceptional for `k < n`
(`Window5.loop_noexc`), and `R = (XZ : Y : Z³)` with `Y = 1` for `O`. For
`k ≥ n` (whose result the callers do not use) the code runs the same way and
writes the same places, and `R` is a triple of some point of the curve.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- `R = O` and `rbx = J`. -/
theorem jinit_ok (hL : JacWinLay K size) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    {base : Addr} {P : Point C} {s₀ s : State} {k : Nat} (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J)
    (hf : JFrame K C base size s₀ s) (hT : TblOk K C base P 16 s) :
    WP isa (.block K.init) s (JInv K C base size P s₀ k K.J) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hJ := hL.J
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact hL.le (by jw_mem)
  have axy : K.R.x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ K.R.x :=
    hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)
  have axz : K.R.x + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.x :=
    hL.ap_oth (i := 0) (j := 2) (by decide) (by decide) (by decide)
  have ayz : K.R.y + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.y :=
    hL.ap_oth (i := 1) (j := 2) (by decide) (by decide) (by decide)
  rw [JacWinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega)) fun s₅ ⟨b₅, k₅⟩ => ?_
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := le x hx; omega
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [m₅, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [m₅, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [m₅, e₄]
  have U : Unch base (jwLoopW K) s.mem s₅.mem := by
    rw [m₅]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)
  have hc : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := sub_powClob (by decide)
  have F₅ := hf.next hL (hs₄.of_keeps k₅ (by decide)) ((((k₂.mono hc).trans (k₃.mono hc)).trans (k₄.mono hc)).trans
    ((Keeps.regs k₅).mono (sub_powClob (by decide)))) U (jwLoopW_sub K)
  have hk' : k + 16 * Window5.geom K.J < 32 ^ K.J := by rw [← offset_eq]; exact hkJ
  refine ⟨⟨.infinity, rfl, fun _ => by rw [Window5.winE_top hk', Window5.mul_zero_pt],
    F₅, hT.loopW hL U hn (by decide), fun x hx => ?_, ?_⟩, b₅⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hp0
    · rw [vy]; exact hone_lt
    · rw [vz]; exact hp0
  · refine Or.inl ⟨rfl, ?_⟩
    show toM _ _ _ = 0
    rw [vz]; exact toM_zero _ _

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`; only `powClob` and `jwW`
change. -/
theorem winJac_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
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
  refine WP.seq (WP.mono (build_ok hL hp hC hM3 hO hD hP hP0 (by omega) hs hM hF) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jinit_ok hL hpn hone_lt hkJ F₁ T₁) fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInv K C base size P s k 0 t)
    (Inv := fun j t => JInv K C base size P s k j t) (n := K.J)
    (fun j t h1 h2 hi => jstep_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hF h1 h2 hi)
    (fun _ h => h) hJ.1 I₂) fun s₃ I₃ => ?_)
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
