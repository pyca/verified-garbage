import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTimingStep

/-! Public table construction has equal traces for equal input field values. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafTable_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hOne : K.one<C.p) (hc : NafTableChecks K F) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter)
      (Naf.table K F) (NafTablePair K C base size 8) := by
  let I := fun j s t => 1≤j ∧ j≤7 ∧ NafTablePair K C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (Naf.tableStep K F) (fun s t =>
      eval .b s=eval .b t ∧
      (eval .b s=some false → NafTablePair K C base size 8 s t) ∧
      (eval .b s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (nafTable_step_relCT hL hW hJ hm hOne (m:=8-j) (by omega) hc).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        refine ⟨cs.trans ct.symm,fun he => ?_,fun he => ?_⟩
        · change s.cf=some false at he
          have hn := of_decide_eq_false (Option.some.inj (cs.symm.trans he))
          have hj1 : j=1 := by omega
          subst j
          exact hp
        · change s.cf=some true at he
          have hy := of_decide_eq_true (Option.some.inj (cs.symm.trans he))
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          rw [show 8-(j-1)=8-j+1 from by omega]
          exact hp
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  unfold Naf.table
  apply RelCT.assoc
  apply RelCT.seq (nafTable_init_relCT hL hW hm hc)
  exact (RelCT.loop I step 7).mono (fun _ _ hp => ⟨by decide,by decide,hp⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.X86
