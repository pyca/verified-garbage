import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

structure DigitChecks : Prop where
  entry : EntryChecks
  add : Checks
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead K))

theorem digit_relCT {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hj : j<257) (hc : DigitChecks)
    {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (CachedJac.digit K ops)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E' s t) := by
  have digit : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.digitRead K))
      (fun s t => FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointStable cfg C base P u v s ∧ JointStable cfg C base P u v t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok hp.left.scr (by decide) (by change 1824+j<size; omega) ps (cs.peer.bits j hj) .x2
    obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok hp.right.scr (by decide) (by change 1824+j<size; omega) pt (ct.peer.bits j hj) .x2
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
      cs.of_mem ks.mem,ct.of_mem kt.mem,
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,vs,vt⟩
  rw [CachedJac.digit]
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2⟩
    change some (s.read .x .x2 != 0) = some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2⟩,hn⟩ es et
    have anz : FastNaf.magnitude 5 v j≠0 := by
      intro hz
      have hb : FastNaf.byte 5 v j=0 := (FastNaf.byte_zero_iff 5 v j).mpr hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hb] at hn
      contradiction
    have entry := entry_relCT (base:=base) (P:=P) (E:=E) (u:=u) (v:=v)
      hL (by omega) hm hj
      (by rw [magnitude_byte]; omega) (by rw [magnitude_byte]; exact FastNaf.magnitude_le (Or.inl rfl) v j) hc.entry
    have add := fun E' => sum_relCT (base:=base) (E:=E') hL hsize hm hOne hc.add hc.copy
    exact (RelCT.seq entry (RelCT.exists_ add)) _ _ _ _ _ _
      ⟨hp,cs,ct,s19,t19,s2,t2⟩ es et
  · intro s t ts tt s' t' ⟨⟨hp,_,_,_,_,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64.CachedField
