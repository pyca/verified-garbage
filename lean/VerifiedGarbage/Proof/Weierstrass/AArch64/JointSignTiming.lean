import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem jointSign_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hj : j<257) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
      JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Joint.signEntry c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  have hbytes : c.gBits+j<size := by
    have := hL.layout.stableBounds (c.gBits,257) (by simp [jointStableRanges]); dsimp only at this; omega
  have sign : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
      JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.signRead c.G))
      (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
        s.gpr .x3=BitVec.ofNat 64 (nafNegative (FastNaf.byte 7 u j)).toNat ∧
        t.gpr .x3=BitVec.ofNat 64 (nafNegative (FastNaf.byte 7 u j)).toNat) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafSignRead_ok (K:=c.G) hp.left.scr hL.gBits hbytes s19 (ss.generator j hj)
    obtain ⟨_,_,xt,vt,kt⟩ := nafSignRead_ok (K:=c.G) hp.right.scr hL.gBits hbytes t19 (st.generator j hj)
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
  rw [Joint.signEntry]
  apply RelCT.seq sign
  apply RelCT.ite
  · intro s t ⟨_,s3,t3⟩
    change some (s.read .x .x3 != 0)=some (t.read .x .x3 != 0)
    rw [VG.Proof.Ed25519.AArch64.read_x,VG.Proof.Ed25519.AArch64.read_x,s3,t3]
  · have op := fprogB_relCT (base:=base) (V:=[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) (E:=E)
      hL.layout.lay hL.layout.aligned (callOf_small (Nat.le_of_eq hL.layout.n)) hm [FOp.sub c.K.E.y c.K.zero c.K.E.y] hc.neg (by
        intro o ho x hx
        rw [List.mem_singleton.mp ho] at hx
        simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact jointEntry_slots c _ (by simp)
        · simp [jointSlots,jacWinSlots,winRo]
        · exact jointEntry_slots c _ (by simp)) (by
        simp [readsOk,FOp.ins,jointLive,nafLive,winRo])
    exact op.mono (fun _ _ h => h.1.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩)
  · exact RelCT.block_nil (fun _ _ h => ⟨_,h.1.1⟩)

end VG.Proof.Weierstrass.AArch64
