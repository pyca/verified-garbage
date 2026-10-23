module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog

/-! # General-curve addition followed by accumulator copy for the table comb -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

structure GeneralSumPost (K : CombCfg) (C : Curve) (b : Fin C.p) (base : Addr) (size : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.A.x, tmv C K.M.n base s' K.A.y, tmv C K.M.n base s' K.A.z) =
    VG.Proof.Weierstrass.rcbAdd (tmv C K.M.n base s K.S.a) b
      (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
      (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)

/-- `A = A + E` by the complete addition into `D`, then copied. -/
theorem generalSumCore_ok {K : CombCfg} {C : Curve} {base : Addr} {size : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E, wordsVal s.mem base x K.M.n < C.p)
    (hApart : RcbApart { K.S with b3 := K.neg } K.A K.E K.D) :
    WP isa (.seq (fprogB K.M (rcb { K.S with b3 := K.neg } K.A K.E K.D)) (.block (copyPt K.M.n K.A K.D))) s
      (GeneralSumPost K C (tmv C K.M.n base s K.neg) base size s) := by
  have hn := hs.nowrap
  have hR : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  have hI : Inv K.M base size C.p (· ∈ combSlots K) (rcbR { K.S with b3 := K.neg } K.A K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, hR, hlt, fun _ _ => rfl⟩
  have hSl : ∀ x ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> comb_mem
  have W := rcb_ok hL.lay hA.al hp hApart hSl (hA.low hSl) hI (fun x hx => hx)
  refine WP.seq (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁, _⟩ := h₁
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  have al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  have axd := hL.apart₂ (x := K.A.x) (y := K.D.x) (by comb_mem) (by comb_mem) (by grind)
  have ayd := hL.apart₂ (x := K.A.y) (y := K.D.y) (by comb_mem) (by comb_mem) (by grind)
  have azd := hL.apart₂ (x := K.A.z) (y := K.D.z) (by comb_mem) (by comb_mem) (by grind)
  have axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dxay := hL.apart₂ (x := K.D.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have dxaz := hL.apart₂ (x := K.D.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dyaz := hL.apart₂ (x := K.D.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have W2 := copy_ok K.M.n hs₁ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have dyax := hL.apart₂ (x := K.D.y) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzax := hL.apart₂ (x := K.D.z) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzay := hL.apart₂ (x := K.D.z) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have hDx : K.D.x ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  have hDy : K.D.y ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  have hDz : K.D.z ∈ rcbW { K.S with b3 := K.neg } K.D ++ rcbR { K.S with b3 := K.neg } K.A K.E := by simp [rcbW]
  have bAx := b64 K.A.x (by comb_mem)
  have bAy := b64 K.A.y (by comb_mem)
  have bAz := b64 K.A.z (by comb_mem)
  have bDx := b64 K.D.x (by comb_mem)
  have bDy := b64 K.D.y (by comb_mem)
  have bDz := b64 K.D.z (by comb_mem)
  have wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]


/-- Refresh `3b` in the negation scratch, then add with the general formula. -/
theorem generalSum_ok {K : CombCfg} {C : Curve} {base : Addr} {size b : Nat}
    (hL : CombLay K size) (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hb : b < C.p)
    {s : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (.block (setConst K.M.n K.neg b))
      (.seq (fprogB K.M (rcb { K.S with b3 := K.neg } K.A K.E K.D))
        (.block (copyPt K.M.n K.A K.D)))) s
      (GeneralSumPost K C (toM C.p (2 ^ (64 * K.M.n)) b) base size s) := by
  have hn := hs.nowrap
  have hnS : K.neg ∈ combSlots K := by comb_mem
  have hnW : K.neg ∈ combWs K := by comb_mem
  have hne : ∀ x ∈ rcbR K.S K.A K.E, x ≠ K.neg := by
    have hnd := hL.nodup
    have hro := hL.ro
    simp only [combWs, combRo, rcbW, List.cons_append, List.nil_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hro ⊢
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false]
    grind
  have ha : ∀ x ∈ rcbR K.S K.A K.E,
      x + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ x := by
    intro x hx
    apply hL.lay.apart x K.neg _ hnS (hne x hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  have hApart : RcbApart { K.S with b3 := K.neg } K.A K.E K.D := by
    refine ⟨hL.add.nodup, ?_⟩
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.add.apart _ (by simp [rcbR])
    · have hnd := hL.nodup
      simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd ⊢
      grind
    all_goals exact hL.add.apart _ (by simp [rcbR])
  refine WP.seq (WP.mono (setConst_ok hs (n := K.M.n) (o := K.neg) (x := b)
    (hL.lay.le _ hnS) (hA.sl _ hnS) (Nat.lt_trans hb hpn)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hm₁ : ModOkA K.M size C.p s₁.mem base :=
    hM.unch O₁.unch (fun w hw => by
      obtain rfl := List.mem_singleton.mp hw
      exact (hL.lay.mo K.neg hnS).symm) hn
  have read₁ : ∀ x ∈ rcbR K.S K.A K.E,
      wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    exact O₁.wordsVal (ha x hx) (by
      have hxs : x ∈ combSlots K := by
        simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
      have := hL.lay.le x hxs; omega)
  have hl₁ : ∀ x ∈ rcbR { K.S with b3 := K.neg } K.A K.E,
      wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [read₁ _ (by simp [rcbR])]; exact hlt _ (by simp [rcbR])
    · rw [e₁]; exact hb
    all_goals (rw [read₁ _ (by simp [rcbR])]; exact hlt _ (by simp [rcbR]))
  refine WP.mono (generalSumCore_ok hL hA hp hs₁ hm₁ hl₁ hApart) fun s₂ h₂ => ?_
  refine ⟨h₂.scr, ?_, ?_, h₂.lt, ?_⟩
  · exact (k₁.mono fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; simp [clob]).trans h₂.keep
  · exact (O₁.unch.trans h₂.unch).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain rfl := List.mem_singleton.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem hnW)
      · exact hw
  · have v := h₂.val
    simp only [tmv] at v ⊢
    rw [e₁] at v
    rw [read₁ K.S.a (by simp [rcbR]), read₁ K.A.x (by simp [rcbR]),
      read₁ K.A.y (by simp [rcbR]), read₁ K.A.z (by simp [rcbR]),
      read₁ K.E.x (by simp [rcbR]), read₁ K.E.y (by simp [rcbR]),
      read₁ K.E.z (by simp [rcbR])] at v
    exact v

end VG.Proof.Weierstrass.AArch64
