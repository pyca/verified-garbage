module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming

/-! ### `Weierstrass.AArch64.JointSignTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem jointSign_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size)
    (_hm : UnitMod C.p (2^(64*c.K.M.n))) (hj : j<257) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
      JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Joint.signEntry c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  have hgl := hL.layout.stableBounds (c.gBits,jointGLen c) (by simp [jointStableRanges])
  have sign : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
      JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Joint.signRead c))
      (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E s t ∧
        s.gpr .x3=BitVec.ofNat 64 (FastNaf.negative c.gw u j).toNat ∧
        t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative c.gw u j).toNat) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := jointSignRead_ok hp.left.scr hL.layout.gw hL.gBits hj hgl s19 ss.generator
    obtain ⟨_,_,xt,vt,kt⟩ := jointSignRead_ok hp.right.scr hL.layout.gw hL.gBits hj hgl t19 st.generator
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
  · have op := subRaw_relCT (base:=base) (V:=[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) (E:=E)
      hL.layout.lay hL.layout.aligned hc.neg (o:=c.K.E.y) (a:=c.K.zero) (b:=c.K.E.y) (by
        intro x hx
        simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact jointEntry_slots c _ (by simp)
        · simp [jointSlots,jacWinSlots,winRo]
        · exact jointEntry_slots c _ (by simp)) (by
        simp [FOp.ins,jointLive,nafLive,winRo])
    exact op.mono (fun _ _ h => h.1.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩)
  · exact RelCT.block_nil (fun _ _ h => ⟨_,h.1.1⟩)

end VG.Proof.Weierstrass.AArch64

end

end


@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem jointEntry_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hj : j<257)
    (hm0 : FastNaf.magnitude c.gw u j≠0) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=jointGCell c u j ∧ t.gpr .x2=jointGCell c u j ∧
      (c.gw=9 → s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64) ∧
      (c.gw=9 → t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64))
      (Joint.fixedEntry c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  have lookup : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=jointGCell c u j ∧ t.gpr .x2=jointGCell c u j ∧
      (c.gw=9 → s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64) ∧
      (c.gw=9 → t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64))
      (.block (Joint.fixedIndex c++Joint.fixedLoad c))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t ∧
        JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
        s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,s19,t19,s2,t2,s3,t3⟩ es et
    obtain ⟨he,E',pair⟩ := jointLookup_relCT hL hC hm0 hc _ _ _ _ _ _ ⟨hp,⟨cs,s2,s3⟩,⟨ct,t2,t3⟩⟩ es et
    obtain ⟨_,_,xs,ks,cs',_,_,_⟩ := jointLookup_generator_ok hL cs s2 s3 hm0
    obtain ⟨_,_,xt,kt,ct',_,_,_⟩ := jointLookup_generator_ok hL ct t2 t3 hm0
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    exact ⟨he,E',pair,cs'.stable,ct'.stable,(ks.gpr _ (x19_not_clob _)).trans s19,
      (kt.gpr _ (x19_not_clob _)).trans t19⟩
  rw [Joint.fixedEntry]
  apply RelCT.seq lookup
  apply RelCT.exists_
  intro E'
  exact jointSign_relCT hL hm hj hc

end VG.Proof.Weierstrass.AArch64
