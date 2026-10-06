import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStep

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
