import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntryLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoadTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit

/-! ## `CachedLoadTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

abbrev lookupCode := Naf.digitIndex++CachedJac.load++Jacobian.publicEntry K

theorem lookupFields_ok {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=b.setWidth 64)
    (ha : 1≤(nafMagnitude b+1)/2) (ha8 : (nafMagnitude b+1)/2≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
      (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).z,
      6000+64*((nafMagnitude b+1)/2-1),6032+64*((nafMagnitude b+1)/2-1)],x∈V) :
    WP isa (.block lookupCode) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
        (E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
         E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).z) ∧
      tmv C K.M.n base t 5400=E (6000+64*((nafMagnitude b+1)/2-1)) ∧
      tmv C K.M.n base t 5432=E (6032+64*((nafMagnitude b+1)/2-1)) := by
  rw [lookupCode,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2,ku⟩ => ?_
  refine WP.mono (entryLoadFields_ok hL hAl hsize (hi.of_keeps ku (by decide)) u2 ha ha8 hD hT)
    fun t ⟨kt,it,vt,v2,v3⟩ => ⟨?_,it,vt,v2,v3⟩
  exact (keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])).trans kt

theorem lookup_relCT {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C}
    (ha : 1≤(nafMagnitude b+1)/2) (ha8 : (nafMagnitude b+1)/2≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
      (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).z,
      6000+64*((nafMagnitude b+1)/2-1),6032+64*((nafMagnitude b+1)/2-1)],x∈V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2])) (.block lookupCode)) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x2=b.setWidth 64 ∧ t.gpr .x2=b.setWidth 64) (.block lookupCode)
      (fun s t => ∃ E',FieldPair K.M base size C.p Sl (entryLive V) E' s t) := by
  let a := (nafMagnitude b+1)/2
  let p := Jacobian.tablePt K a
  let F := fun x => if x=K.E.x then E p.x else if x=K.E.y then E p.y else if x=K.E.z then E p.z
    else if x=5400 then E (6000+64*(a-1)) else E (6032+64*(a-1))
  apply fieldWrite_relCT (F:=F) hL hct
  · intro s t hp ps pt
    refine ⟨hp.sp,fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
    · exact ps.trans pt.symm
  · exact hD
  · intro x hx
    simp only [entryLive,entryWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · intro s hi hp
    refine WP.mono (lookupFields_ok hL hAl hsize hi hp ha ha8 hD hT) fun t ⟨hk,it,vt,v2,v3⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx
    simp only [Prod.mk.injEq] at vt
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · simpa only [F,ite_true] using vt.1
    · simpa only [F,show K.E.y≠K.E.x by decide,ite_false,ite_true] using vt.2.1
    · simpa only [F,show K.E.z≠K.E.x by decide,show K.E.z≠K.E.y by decide,ite_false,ite_true] using vt.2.2
    · simpa only [F,show 5400≠K.E.x by decide,show 5400≠K.E.y by decide,show 5400≠K.E.z by decide,ite_false,ite_true] using v2
    · simpa only [F,show 5432≠K.E.x by decide,show 5432≠K.E.y by decide,show 5432≠K.E.z by decide,
        show (5432:Nat)≠5400 by decide,ite_false] using v3

end VG.Proof.Weierstrass.AArch64.CachedField

end

/-! ## `CachedEntryTiming` -/

section

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
  · have op := fprogB_relCT (base:=base) (V:=entryLive (jointLive cfg)) (E:=E') hL.lay hL.aligned (callOf_small (Nat.le_of_eq hL.n)) hm
      [FOp.sub K.E.y K.zero K.E.y] hc.neg (by decide +kernel) (by decide +kernel)
    exact op.mono (fun _ _ h => h.1.1) (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩)
  · intro s t ts tt s' t' ⟨⟨hp,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64.CachedField

end

/-! ## `CachedSumTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem sum_relCT {C : Curve} {base : Addr} {size : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hc : Checks) (hcopy : FieldCT (.block (copyPt 4 K.R K.D))) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E)
      (.seq (CachedJac.add K ops) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E' s t) := by
  have ha := add_relCT (base:=base) (E:=E) (V:=entryLive (jointLive cfg)) hL.lay hL.aligned hm hsize
    (by decide +kernel) (by decide +kernel) hOne hc
  apply RelCT.seq ha
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.lay hL.aligned
    (o:=K.R) (q:=K.D) (V:=[K.D.x,K.D.y,K.D.z]++entryLive (jointLive cfg))
    (by decide +kernel) (by decide +kernel) hcopy
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (by
    intro x hx
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hx))))⟩)

end VG.Proof.Weierstrass.AArch64.CachedField

end

/-! ## `CachedDigitTiming` -/

section

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

end
