import VerifiedGarbage.Proof.Weierstrass.X86.NafInvariant

/-! A Jacobian doubling with no intermediate homogeneous conversion. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafDoubleCore_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} (hL : NafLay K size)
    (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s : State} (h : NafCore K C base size P β e s) :
    WP isa (.seq (fprog F (dblJMul K.S K.R K.D)) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ NafCore K C base size P β (2*e) t := by
  have old := hL.toWinLay hJ
  have sl (p o : Pt) (hp : p=K.R ∨ p=K.D) (ho : o=K.R ∨ o=K.D) :
      ∀ x∈rcbW K.S o++rcbR K.S p p,x∈nafSlots K := by
    intro x hx; apply hL.old_slots x
    rcases hp with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have vr : ∀ x∈rcbR K.S K.R K.R,x∈nafLive K := by
    intro x hx
    simp only [rcbR,nafLive,nafTableLive,jacCoords,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have vd : ∀ x∈rcbR K.S K.D K.D,x∈jacCoords K.D++nafLive K := by
    intro x hx
    simp only [rcbR,nafLive,nafTableLive,jacCoords,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have ww (o : Pt) (ho : o=K.R ∨ o=K.D) : ∀ x∈rcbW K.S o,x∈winOther K := by
    intro x hx
    rcases ho with rfl | rfl <;>
      simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  apply WP.seq
  refine WP.mono (jacDouble_ok hL.lay hAcc hm hC ha (old.rcbApart_D (Or.inl rfl))
    (sl _ _ (Or.inl rfl) (Or.inr rfl)) h.field vr (hC.onCurve_mul hP _) h.point)
    fun t ⟨kt,it,jt⟩ => ?_
  rw [←hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAcc hL.rcbApart_DR
    (sl _ _ (Or.inr rfl) (Or.inl rfl)) it vd) fun u ⟨E',ku,iu,hu⟩ => ?_
  have kp := (kt.mono (ww _ (Or.inr rfl))).trans (ku.mono (ww _ (Or.inl rfl)))
  refine ⟨kp,h.next hL hAcc hBitsWk kp
    (iu.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))) ?_⟩
  simp only [Prod.mk.injEq] at hu
  rw [hu.1,hu.2.1,hu.2.2]
  rw [hC.add_mul_mul hP,show e+e=2*e by omega] at jt
  exact jt

end VG.Proof.Weierstrass.X86
