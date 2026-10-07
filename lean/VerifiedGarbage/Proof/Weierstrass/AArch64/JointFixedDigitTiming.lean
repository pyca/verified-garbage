import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntryTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem jointFixedSum_relCT (certs : Forward.Arithmetic.Cases)
    {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointFixedLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hsize : 8192≤size) (hOne : c.K.one<C.p) (hc : JointFixedChecks c) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c)
      ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E)
      (.seq (Joint.mixedAdd c.K c.K.R c.K.E c.K.D) (.block (copyPt 4 c.K.R c.K.D)))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c := by intro x hx; jslots
  apply RelCT.seq (jointMixedAdd_relCT certs hL.layout.lay hL.layout.aligned hm hsize hL.addApart sl vr hOne hc.mixed)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.layout.lay hL.layout.aligned
    (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
    (V:=[c.K.D.x,c.K.D.y,c.K.D.z]++([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c))
    (by intro x hx; exact List.mem_append_left _ hx) (by rw [hL.layout.n]; exact hc.copy)
  rw [hL.layout.n] at cp
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun x hx => by simp [hx])⟩)

theorem jointFixedDigit_relCT (certs : Forward.Arithmetic.Cases)
    {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hsize : 8192≤size)
    (hOne : c.K.one<C.p) (hj : j<257) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Joint.fixedDigit c (Joint.mixedAdd c.K c.K.R c.K.E c.K.D))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have hbytes : c.gBits+j<size := by
    have := hL.layout.stableBounds (c.gBits,257) (by simp [jointStableRanges]); dsimp only at this; omega
  have digit : RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.digitRead c.G))
      (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok (K:=c.G) hp.left.scr hL.gBits hbytes ps (cs.stable.generator j hj) .x2
    obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok (K:=c.G) hp.right.scr hL.gBits hbytes pt (ct.stable.generator j hj) .x2
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm
    have frame {a b : State} (hk : VG.Proof.Ed25519.AArch64.Keeps [.x2,.x16] a b) :
        ProgKeep c.K.M base [] a b := keeps_prog hk (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp [clob])
    refine ⟨hc.read _ _ _ _ _ _ trivial trivial pub es et,
      ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      cs.of_keeps ks (by decide) (cs.external.keep (frame ks) (Exec.syms es) (by simp) cs.field.mod.tmp),
      ct.of_keeps kt (by decide) (ct.external.keep (frame kt) (Exec.syms et) (by simp) ct.field.mod.tmp),
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,vs,vt⟩
  rw [Joint.fixedDigit]
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2⟩
    change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2⟩,hn⟩ es et
    have anz : FastNaf.magnitude 7 u j≠0 := by
      intro hz
      have hb : FastNaf.byte 7 u j=0 := (FastNaf.byte_zero_iff 7 u j).mpr hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hb] at hn
      contradiction
    have entry := jointEntry_relCT (base:=base) (T:=T) (G:=G) (Q:=Q) (A:=A) (E:=E) (v:=v) hL hC hm hj anz hc
    have sum := fun E' => jointFixedSum_relCT certs (base:=base) (E:=E') hL hm hsize hOne hc
    exact (RelCT.seq entry (RelCT.exists_ sum)) _ _ _ _ _ _ ⟨hp,cs,ct,s19,t19,s2,t2⟩ es et
  · exact RelCT.block_nil (fun _ _ h => ⟨_,h.1.1⟩)

end VG.Proof.Weierstrass.AArch64
