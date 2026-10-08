import VerifiedGarbage.Proof.Weierstrass.X86.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Construction of the eight odd multiples used by the public verifier. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- Build `P, 3P, …, 15P`, retaining the double in the ninth point. -/
theorem nafTable_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
     (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.table K F) s (fun t => NafTableInv K C base size wk P s t 8) := by
  unfold Naf.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hAcc hJ hm hC ha hP hI hJP) fun a ia => ?_)
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤7 ∧ NafTableInv K C base size wk P s t (8-j))
    (fun j u ⟨hj,hj7,hu⟩ => ?_) 7 a ⟨by decide,by decide,ia⟩
  refine WP.mono (nafTable_step_ok hL hAcc hJ hm hC ha hOne hP (by omega) (by omega) hu)
    fun t ⟨it,cf⟩ => ?_
  by_cases hj1 : j=1
  · subst j
    exact Or.inl ⟨cf,it⟩
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,?_⟩
    · change t.cf=some true
      rw [cf]; exact congrArg some (decide_eq_true (by omega))
    · rw [show 8-(j-1)=8-j+1 from by omega]
      exact it

/-- Table construction leaves the recoded scalar bytes intact. -/
theorem NafTableInv.digits {K : WinCfg} {C : Curve} {base : Addr} {size m wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State} (hL : NafLay K size) (hBitsWk : K.bits+260≤wk)
    (hI : NafTableInv K C base size wk P s t m)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=β i) :
    ∀ i<257, t.mem (off base (K.bits+i))=β i := by
  intro i hi
  rw [hI.unch.byte (fun w hw => ?_) (by have := hL.bits; have := hI.field.scr.nowrap; omega),hb i hi]
  simp only [nafTableWrites,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
  · have hb' := hL.bits_w x hx
    dsimp only; rw [hL.n]; omega
  · have hb' := hL.bits_tmp
    dsimp only; rw [hL.n]; omega

  · dsimp only; omega
  · have := hL.bits; have := hL.size_le
    dsimp only [Mont.outW]; omega

end VG.Proof.Weierstrass.X86
