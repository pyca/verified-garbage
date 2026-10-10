import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop

/-! ## `JacWindowDigitTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

structure JacDigitChecks (K : WinCfg) : Prop where
  entry : JacEntryChecks K
  add : JacAddChecks K K.R K.E K.D
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (winIndex 5 ++ hornerBits K.bits 5 ++ magnitudeH 16))

theorem jacDigit_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hj : j<52) (hc : JacDigitChecks K)
    {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t ∧
      JacCore K C base size P k e s ∧ JacCore K C base size P k e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Jacobian.jacDigitAdd K 5)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t) := by
  let T : TCombCfg := ⟨K.M,K.S,K.R,K.E,K.D,K.neg,K.zero,K.bits,260,"",5,52,(0,0),K.one⟩
  let a := magH 16 (Window5.nib k j)
  have ha : a≤16 := magH_le (Nat.mod_lt _ (by decide))
  have digit : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t ∧
      JacCore K C base size P k e s ∧ JacCore K C base size P k e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block T.digit)
      (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t ∧
      JacCore K C base size P k e s ∧ JacCore K C base size P k e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=BitVec.ofNat 64 a ∧ t.gpr .x2=BitVec.ofNat 64 a) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := digitW_ok T hp.left.scr (k:=k) (j:=j) (N:=260)
      (by simp [T]) (by simp [T]) (by dsimp [T]; omega) hL.bits hBits ps cs.stable.bits
    obtain ⟨_,_,xt,vt,kt⟩ := digitW_ok T hp.right.scr (k:=k) (j:=j) (N:=260)
      (by simp [T]) (by simp [T]) (by dsimp [T]; omega) hL.bits hBits pt ct.stable.bits
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm
    refine ⟨hc.digit _ _ _ _ _ _ trivial trivial pub es et,
      ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      cs.of_keeps ks (by decide),ct.of_keeps kt (by decide),
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,?_,?_⟩
    · simpa only [T,TCombCfg.H,Window5.combWin_five] using vs
    · simpa only [T,TCombCfg.H,Window5.combWin_five] using vt
  change RelCT isa _ (.seq (.block T.digit) (.ite (.nonzero .x .x2) (Jacobian.jacSignedAdd K 5) (.block []))) _
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2⟩
    change some (s.read .x .x2 != 0) = some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2⟩,hn⟩ es et
    have anz : a≠0 := by
      intro hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hz] at hn
      contradiction
    have entry := jacSignedEntry_relCT (base:=base) (P:=P) (k:=k) (E:=E) hL hJ hAl hm hTbl hBits hj (by omega : 1≤a) ha hc.entry
    have add := fun E' => jacAddDigit_relCT (base:=base) (E:=E') hL hJ hAl hm hOne hc.add hc.copy
    exact (RelCT.seq entry (RelCT.exists_ add)) _ _ _ _ _ _
      ⟨hp,cs.stable,ct.stable,s19,t19,s2,t2⟩ es et
  · intro s t ts tt s' t' ⟨⟨hp,_,_,_,_,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JacWindowStepTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def JacPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (k e j : Nat) (s t : State) : Prop :=
  (∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t) ∧
  JacCore K C base size P k e s ∧ JacCore K C base size P k e t ∧
  s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

structure JacStepChecks (K : WinCfg) : Prop where
  double : JacDoubleChecks K
  digit : JacDigitChecks K
  dec : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [decCounter])

theorem jacStep_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hj : j<52) (hc : JacStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (JacPair K C base size P k (Window5.winE k 52 (j+1)) (j+1))
      (Jacobian.jacStep K 5) (JacPair K C base size P k (Window5.winE k 52 j) j) := by
  have raw : RelCT isa (JacPair K C base size P k (Window5.winE k 52 (j+1)) (j+1))
      (Jacobian.jacStep K 5)
      (fun s t => ∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t) := by
    intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
    change Exec isa (.seq (.block [decCounter]) (.seq (Jacobian.jacDoubles K 5) (Jacobian.jacDigitAdd K 5))) s ts s' at es
    change Exec isa (.seq (.block [decCounter]) (.seq (Jacobian.jacDoubles K 5) (Jacobian.jacDigitAdd K 5))) t tt t' at et
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
        have pair : FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E _ _ :=
          ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
        have ca := cs.of_keeps ks (by decide)
        have cb := ct.of_keeps kt (by decide)
        cases bs with | seq fs gs =>
          cases bt with | seq ft gt =>
            obtain ⟨hf,E',pair'⟩ := jacFive_relCT hL hJ hAl hm hc.double _ _ _ _ _ _ pair fs ft
            obtain ⟨_,_,xf,kf,cf⟩ := jacFiveCore_ok hL hJ hAl hm hC ha hP ca
            obtain ⟨_,_,xg,kg,cg⟩ := jacFiveCore_ok hL hJ hAl hm hC ha hP cb
            obtain ⟨_,rfl⟩ := Exec.det fs xf
            obtain ⟨_,rfl⟩ := Exec.det ft xg
            have s19 := (kf.gpr _ (x19_not_clob _)).trans vs
            simp only [Nat.add_sub_cancel] at s19
            have t19 := (kg.gpr _ (x19_not_clob _)).trans vt
            simp only [Nat.add_sub_cancel] at t19
            obtain ⟨hg,hp'⟩ := jacDigit_relCT hL hJ hAl hm hOne hTbl hBits hj hc.digit
              _ _ _ _ _ _ ⟨pair',cf,cg,s19,t19⟩ gs gt
            exact ⟨by rw [hd,hf,hg],hp'⟩
  intro s t ts tt s' t' hp es et
  obtain ⟨he,pair⟩ := raw _ _ _ _ _ _ hp es et
  obtain ⟨_,cs,ct,ps,pt⟩ := hp
  obtain ⟨_,_,xs,_,cs',ps'⟩ := jacStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hk hj hP cs ps
  obtain ⟨_,_,xt,_,ct',pt'⟩ := jacStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hk hj hP ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,pair,cs',ct',ps',pt'⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JacWindowLoopTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem jacLoop_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hklt : k<32^52) (hc : JacStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (JacPair K C base size P k 0 52)
      (.loop (Jacobian.jacStep K 5) (.nonzero .x .x19))
      (JacPair K C base size P k (k-16*Window5.geom 52) 0) := by
  let I := fun j s t => 1≤j ∧ j≤52 ∧ JacPair K C base size P k (Window5.winE k 52 j) j s t
  have step : ∀ j, RelCT isa (I j) (Jacobian.jacStep K 5) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → JacPair K C base size P k (k-16*Window5.geom 52) 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj52 : j≤52
      · refine (jacStep_relCT hL hJ hAl hm hC ha hOne hTbl hBits hk (j:=j-1) (by omega) hc hP).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t hp
        have s19 := hp.2.2.2.1
        have t19 := hp.2.2.2.2
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          simpa only [hz,Window5.winE_zero] using hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj52 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 52).mono (fun _ _ h => ⟨by decide,by decide,by
    simpa only [Window5.winE_top hklt] using h⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64

end
