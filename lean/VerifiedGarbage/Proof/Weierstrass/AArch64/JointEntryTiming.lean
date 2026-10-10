import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## `JointFixedTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

structure JointFixedChecks (c : Joint.Cfg) : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.AgreeS [c.tsym] (Taint.ofRegs [.x0,.x2]))
    (.block (Naf.digitIndex++Joint.fixedLoad c))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.signRead c.G))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub c.K.M c.K.E.y c.K.zero c.K.E.y))
  read : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead c.G))
  mixed : JointMixedChecks c.K c.K.R c.K.E c.K.D
  copy : FieldCT (.block (copyPt 4 c.K.R c.K.D))

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointFixedLookupTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

def jointAffineCoords {C : Curve} : Point C → Fe C × Fe C
  | .infinity => (0,0)
  | .affine x y => (x,y)

theorem jointAffine_unique {C : Curve} (hC : Law C) {X Y : Fe C} {P : Point C}
    (h : InvJ C X Y 1 P) : (X,Y)=jointAffineCoords P := by
  rcases h with ⟨_,hz⟩ | h
  · exact False.elim (hC.one_ne_zero hz)
  · simp only [Lean.Grind.Semiring.mul_one] at h
    cases P with
    | infinity => exact False.elim (hC.one_ne_zero h.2.2)
    | affine x y =>
      apply Prod.ext
      · simpa only [Lean.Grind.Semiring.mul_one,jointAffineCoords] using h.2.1
      · simpa only [Lean.Grind.Semiring.mul_one,jointAffineCoords] using h.2.2

theorem jointFieldWrite_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V V' W : List Nat} {E F : Nat → Fin m}
    {code : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) Pub code)
    (hpub : ∀ s t,FieldPair M base size m Sl V E s t → Pre s → Pre t → Pub s t)
    (hW : ∀ x∈W,Sl x) (hV : ∀ x∈V',x∈W ∨ x∈V)
    (hw : ∀ s,Inv M base size m Sl V E s → Pre s → WP isa code s fun t =>
      ∃ E',ProgKeep M base W s t ∧ Inv M base size m Sl V' E' t ∧
        ∀ x∈V',x∈W → E' x=F x) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) code
      (fun s t => ∃ E',FieldPair M base size m Sl V' E' s t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,Es,ks,is,vs⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,Et,kt,it,vt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,Es,?_⟩
  exact hp.rebuild hL ks kt hW is it hV (fun x hx hw => (vs x hx hw).trans (vt x hx hw).symm)

theorem jointLookup_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm0 : FastNaf.magnitude 7 u j≠0) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      (JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
        s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64) ∧
      (JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
        t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64))
      (.block (Naf.digitIndex++Joint.fixedLoad c))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  let P := mul (FastNaf.magnitude 7 u j) G
  let F := fun x => if x=c.K.E.x then (jointAffineCoords P).1 else
    if x=c.K.E.y then (jointAffineCoords P).2 else 1
  apply jointFieldWrite_relCT (F:=F) hL.layout.lay hc.lookup
  · intro s t hp ps pt
    refine ⟨⟨hp.sp,fun r hr => ?_⟩,?_⟩
    · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.2.trans pt.2.symm
    · intro n hn; rw [List.mem_singleton.mp hn]
      exact ps.1.external.symbol.trans pt.1.external.symbol.symm
  · exact jointEntry_slots c
  · intro x hx; exact List.mem_append.mp hx
  · intro s _ hs
    refine WP.mono (jointLookup_generator_ok hL hs.1 hs.2 hm0) fun t ⟨kt,_,it,jt,zt⟩ => ⟨_,kt,it,?_⟩
    rw [zt] at jt
    have he := jointAffine_unique hC jt
    have hex := congrArg Prod.fst he
    have hey := congrArg Prod.snd he
    have hn := hL.entryNodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    intro x _ hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,ite_true] using hex
    · simpa only [F,Ne.symm hn.1.1,ite_false,ite_true] using hey
    · simpa only [F,Ne.symm hn.1.2,Ne.symm hn.2.1,ite_false] using zt

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointSignTiming` -/

section

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

end

/-! ## `JointEntryTiming` -/

section

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

end
