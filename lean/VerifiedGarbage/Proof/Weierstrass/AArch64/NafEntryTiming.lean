import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| simp only [nafLive,jacWinSlots,jacWinWrites,
  winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

structure NafEntryChecks (K : WinCfg) : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2]))
    (.block (Naf.digitIndex ++ Jacobian.publicEntry K))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.signRead K))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y))

theorem nafEntry_relCT {K : WinCfg} {C : Curve} {base : Addr} {size j : Nat}
    {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    (hj : j<257) (hmag : 1≤nafMagnitude (β j)) (hmag15 : nafMagnitude (β j)≤15)
    (hc : NafEntryChecks K) {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafStable K C base P β s ∧ NafStable K C base P β t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(β j).setWidth 64 ∧ t.gpr .x2=(β j).setWidth 64)
      (Naf.signedEntry K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacCoords K.E++nafLive K) E' s t) := by
  let a := (nafMagnitude (β j)+1)/2
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have hD : ∀ x∈jacCoords K.E, x∈jacWinSlots K := by
    intro x hx; simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem
  have hT : ∀ x∈jacCoords (Jacobian.tablePt K a), x∈nafLive K := by
    intro x hx
    apply List.mem_append_right
    simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩
  have hap : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x := by
    have hx := hL.tbl K.E.x (by jmem)
    have hy := hL.tbl K.E.y (by jmem)
    have hz := hL.tbl K.E.z (by jmem)
    rw [hL.exy] at hy
    rw [hL.exz] at hz
    omega
  have load := nafPublic_relCT (base:=base) (E:=E) (b:=β j) hL.lay hAl hL.n hL.exy hL.exz hD hT hap ha hTbl hc.lookup
  have load' : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafStable K C base P β s ∧ NafStable K C base P β t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(β j).setWidth 64 ∧ t.gpr .x2=(β j).setWidth 64)
      (.block (Naf.digitIndex ++ Jacobian.publicEntry K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacCoords K.E++nafLive K) E' s t ∧
        NafStable K C base P β s ∧ NafStable K C base P β t ∧
        s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19,s2,t2⟩ es et
    obtain ⟨he,E',pair⟩ := load _ _ _ _ _ _ ⟨hp,s2,t2⟩ es et
    obtain ⟨_,_,xs,ks,_,_⟩ := nafPublicFields_ok hL.lay hAl hL.n hL.exy hL.exz hp.left s2 ha hTbl hD hT hap
    obtain ⟨_,_,xt,kt,_,_⟩ := nafPublicFields_ok hL.lay hAl hL.n hL.exy hL.exz hp.right t2 ha hTbl hD hT hap
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have hw : ∀ x∈[K.E.x,K.E.y,K.E.z], x∈winOther K := by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jmem
    exact ⟨he,E',pair,
      ss.keep hL hJ hp.left.scr.nowrap (ks.mono hw).unch,
      st.keep hL hJ hp.right.scr.nowrap (kt.mono hw).unch,
      (ks.gpr _ (x19_not_clob _)).trans s19,(kt.gpr _ (x19_not_clob _)).trans t19⟩
  rw [Naf.signedEntry]
  apply RelCT.seq load'
  apply RelCT.exists_
  intro E'
  have sign : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacCoords K.E++nafLive K) E' s t ∧
      NafStable K C base P β s ∧ NafStable K C base P β t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.signRead K))
      (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacCoords K.E++nafLive K) E' s t ∧
        s.gpr .x3=BitVec.ofNat 64 (nafNegative (β j)).toNat ∧
        t.gpr .x3=BitVec.ofNat 64 (nafNegative (β j)).toNat) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafSignRead_ok hp.left.scr hBits (by have := hL.bits; omega) s19 (ss.bits j hj)
    obtain ⟨_,_,xt,vt,kt⟩ := nafSignRead_ok hp.right.scr hBits (by have := hL.bits; omega) t19 (st.bits j hj)
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact s19.trans t19.symm
    exact ⟨hc.sign _ _ _ _ _ _ trivial trivial pub es et,
      ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,vs,vt⟩
  apply RelCT.seq sign
  apply RelCT.ite
  · intro s t ⟨_,s3,t3⟩
    change some (s.read .x .x3 != 0)=some (t.read .x .x3 != 0)
    rw [VG.Proof.Ed25519.AArch64.read_x,VG.Proof.Ed25519.AArch64.read_x,s3,t3]
  · have op := fprogB_relCT (base:=base) (V:=jacCoords K.E++nafLive K) (E:=E') hL.lay hAl hm
      [FOp.sub K.E.y K.zero K.E.y] hc.neg (by
        intro o ho x hx
        rw [List.mem_singleton.mp ho] at hx
        simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl <;> jmem) (by
        simp [readsOk, FOp.ins, jacCoords, nafLive, winRo])
    exact op.mono (fun _ _ h => h.1.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩)
  · intro s t ts tt s' t' ⟨⟨hp,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64
