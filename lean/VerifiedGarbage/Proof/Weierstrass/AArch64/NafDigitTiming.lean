import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

structure NafDigitChecks (K : WinCfg) : Prop where
  entry : NafEntryChecks K
  add : JacAddChecks K K.R K.E K.D
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead K))

theorem nafDigit_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<257) (hc : NafDigitChecks K)
    {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Naf.digit K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) := by
  have digit : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.digitRead K))
      (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(Naf5.byte k j).setWidth 64 ∧ t.gpr .x2=(Naf5.byte k j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok hp.left.scr hBits (by have := hL.bits; omega) ps (cs.stable.bits j hj) .x2
    obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok hp.right.scr hBits (by have := hL.bits; omega) pt (ct.stable.bits j hj) .x2
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
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,vs,vt⟩
  rw [Naf.digit]
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2⟩
    change some (s.read .x .x2 != 0) = some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2⟩,hn⟩ es et
    have anz : Naf5.magnitude k j≠0 := by
      intro hz
      have hb : Naf5.byte k j=0 := (Naf5.byte_zero_iff k j).mpr hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hb] at hn
      contradiction
    have entry := nafEntry_relCT (base:=base) (P:=P) (E:=E) (β:=Naf5.byte k) hL hJ hAl hm hTbl hBits hj
      (by rw [nafMagnitude_byte]; omega) (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j) hc.entry
    have add := fun E' => nafAdd_relCT (base:=base) (E:=E') hL hJ hAl hm hOne hc.add hc.copy
    exact (RelCT.seq entry (RelCT.exists_ add)) _ _ _ _ _ _
      ⟨hp,cs.stable,ct.stable,s19,t19,s2,t2⟩ es et
  · intro s t ts tt s' t' ⟨⟨hp,_,_,_,_,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64
