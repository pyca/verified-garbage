import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoadTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntry
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

structure EntryChecks : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2]))
    (.block (lookupCode))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.signRead K))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y))

theorem entry_relCT {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hj : j<257) (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hc : EntryChecks) {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 5 v j).setWidth 64)
      (CachedJac.entry K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E' s t) := by
  let a := (nafMagnitude (FastNaf.byte 5 v j)+1)/2
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have hD := entry_slots
  have hT := entrySources_live ha ha8
  have load := lookup_relCT (base:=base) (E:=E) (b:=FastNaf.byte 5 v j)
    hL.lay hL.aligned hsize ha ha8 hD hT hc.lookup
  have load' : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 5 v j).setWidth 64)
      (.block (lookupCode))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E' s t ∧
        JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
        s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19,s2,t2⟩ es et
    obtain ⟨he,E',pair⟩ := load _ _ _ _ _ _ ⟨hp,s2,t2⟩ es et
    obtain ⟨_,_,xs,ks,_,_,_,_⟩ := lookupFields_ok hL.lay hL.aligned hsize hp.left s2 ha ha8 hD hT
    obtain ⟨_,_,xt,kt,_,_,_,_⟩ := lookupFields_ok hL.lay hL.aligned hsize hp.right t2 ha ha8 hD hT
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    exact ⟨he,E',pair,
      ss.keep (ks.mono entry_work) (fun r hr => by have := hL.stableBounds r hr; have := hp.left.scr.nowrap; omega) hL.stableSep,
      st.keep (kt.mono entry_work) (fun r hr => by have := hL.stableBounds r hr; have := hp.right.scr.nowrap; omega) hL.stableSep,
      (ks.gpr _ (x19_not_clob _)).trans s19,(kt.gpr _ (x19_not_clob _)).trans t19⟩
  rw [CachedJac.entry]
  apply RelCT.seq load'
  apply RelCT.exists_
  intro E'
  have sign : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E' s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.signRead K))
      (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E' s t ∧
        s.gpr .x3=BitVec.ofNat 64 (nafNegative (FastNaf.byte 5 v j)).toNat ∧
        t.gpr .x3=BitVec.ofNat 64 (nafNegative (FastNaf.byte 5 v j)).toNat) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafSignRead_ok hp.left.scr (by decide) (by change 1824+j<size; omega) s19 (ss.peer.bits j hj)
    obtain ⟨_,_,xt,vt,kt⟩ := nafSignRead_ok hp.right.scr (by decide) (by change 1824+j<size; omega) t19 (st.peer.bits j hj)
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
  · have op := fprogB_relCT (base:=base) (V:=entryLive (jointLive cfg)) (E:=E') hL.lay hL.aligned hm
      [FOp.sub K.E.y K.zero K.E.y] hc.neg (by decide +kernel) (by decide +kernel)
    exact op.mono (fun _ _ h => h.1.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩)
  · intro s t ts tt s' t' ⟨⟨hp,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64.CachedField
