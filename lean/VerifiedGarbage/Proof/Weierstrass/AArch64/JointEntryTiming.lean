import VerifiedGarbage.Proof.Weierstrass.AArch64.JointSignTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem jointEntry_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hj : j<257)
    (hm0 : FastNaf.magnitude 7 u j≠0) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
      (Joint.fixedEntry c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  have lookup : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64)
      (.block (Naf.digitIndex++Joint.fixedLoad c))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t ∧
        JointStable c C base Q u v s ∧ JointStable c C base Q u v t ∧
        s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,s19,t19,s2,t2⟩ es et
    obtain ⟨he,E',pair⟩ := jointLookup_relCT hL hC hm0 hc _ _ _ _ _ _ ⟨hp,⟨cs,s2⟩,⟨ct,t2⟩⟩ es et
    obtain ⟨_,_,xs,ks,cs',_,_,_⟩ := jointLookup_generator_ok hL cs s2 hm0
    obtain ⟨_,_,xt,kt,ct',_,_,_⟩ := jointLookup_generator_ok hL ct t2 hm0
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
