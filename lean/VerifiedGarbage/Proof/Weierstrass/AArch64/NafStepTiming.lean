import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def NafPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (k e j : Nat) (s t : State) : Prop :=
  (∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t) ∧
  NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
  s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

structure NafStepChecks (K : WinCfg) : Prop where
  double : FieldCT (Naf.double K K.R K.D)
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : NafDigitChecks K
  dec : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [decCounter])

theorem nafStep_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    (hj : j<256) (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k (Naf5.residual k (j+1)) (j+1))
      (Naf.step K) (NafPair K C base size P k (Naf5.residual k j) j) := by
  have raw : RelCT isa (NafPair K C base size P k (Naf5.residual k (j+1)) (j+1))
      (.seq (.block [decCounter]) (.seq (.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D))) (Naf.digit K)))
      (fun s t => ∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t) := by
    intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
    change Exec isa (.seq (.block [decCounter]) (.seq ((.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D)))) (Naf.digit K))) s ts s' at es
    change Exec isa (.seq (.block [decCounter]) (.seq ((.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D)))) (Naf.digit K))) t tt t' at et
    cases es with | seq ds bs =>
      cases et with | seq dt bt =>
        obtain ⟨_,_,xs,vs,ks⟩ := decCounter_ok s (by omega : 1≤j+1) (by omega : j+1<2^64) ps
        obtain ⟨_,_,xt,vt,kt⟩ := decCounter_ok t (by omega : 1≤j+1) (by omega : j+1<2^64) pt
        obtain ⟨_,rfl⟩ := Exec.det ds xs
        obtain ⟨_,rfl⟩ := Exec.det dt xt
        have hd := hc.dec _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
          simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
          subst hr
          exact ps.trans pt.symm⟩ ds dt
        have pair : FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E _ _ :=
          ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
        have ca := cs.of_keeps ks (by decide)
        have cb := ct.of_keeps kt (by decide)
        cases bs with | seq fs gs =>
          cases bt with | seq ft gt =>
            obtain ⟨hf,E',pair'⟩ := nafDouble_relCT hL hJ hAl hm hc.double hc.copy _ _ _ _ _ _ pair fs ft
            obtain ⟨_,_,xf,kf,cf⟩ := nafDoubleCore_ok hL hJ hAl hm hC ha hP ca
            obtain ⟨_,_,xg,kg,cg⟩ := nafDoubleCore_ok hL hJ hAl hm hC ha hP cb
            obtain ⟨_,rfl⟩ := Exec.det fs xf
            obtain ⟨_,rfl⟩ := Exec.det ft xg
            have s19 := (kf.gpr _ (x19_not_clob _)).trans vs
            simp only [Nat.add_sub_cancel] at s19
            have t19 := (kg.gpr _ (x19_not_clob _)).trans vt
            simp only [Nat.add_sub_cancel] at t19
            obtain ⟨hg,hp'⟩ := nafDigit_relCT hL hJ hAl hm hOne hTbl hBits (by omega) hc.digit
              _ _ _ _ _ _ ⟨pair',cf,cg,s19,t19⟩ gs gt
            exact ⟨by rw [hd,hf,hg],hp'⟩
  intro s t ts tt s' t' hp es et
  have regroup : ∀ {u v tr}, Exec isa (Naf.step K) u tr v →
      Exec isa (.seq (.block [decCounter]) (.seq (.seq (Naf.double K K.R K.D)
        (.block (copyPt 4 K.R K.D))) (Naf.digit K))) u tr v := by
    intro u v tr ex
    cases ex with | seq ea eb =>
      cases eb with | seq ec ed =>
        cases ed with | seq ee ef =>
          simpa only [List.append_assoc] using Exec.seq ea (Exec.seq (Exec.seq ec ee) ef)
  obtain ⟨he,pair⟩ := raw _ _ _ _ _ _ hp (regroup es) (regroup et)
  obtain ⟨_,cs,ct,ps,pt⟩ := hp
  obtain ⟨_,_,xs,_,cs',ps'⟩ := nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hj hP cs ps
  obtain ⟨_,_,xt,_,ct',pt'⟩ := nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hj hP ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,pair,cs',ct',ps',pt'⟩

end VG.Proof.Weierstrass.AArch64
