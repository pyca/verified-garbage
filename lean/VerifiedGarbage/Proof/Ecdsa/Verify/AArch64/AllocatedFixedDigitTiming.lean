import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointMixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntryTiming

/-! ## `AllocatedMixedTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem mixedAdd_relCT (raw : RawCorrect) {base : Addr}
    (hm : UnitMod C.p (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fe C} (hV : ∀ x∈rcbR K.S K.R K.E,x∈V)
    (hOne : K.one<C.p) (hc : JointMixedChecks K K.R K.E K.D) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E)
      VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd
      (fun s t => ∃ E',FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V) E' s t) := by
  let hL := JointLayout.layout.lay
  let hAl := JointLayout.layout.aligned
  have hA : RcbApart K.S K.R K.E K.D := apart
  have hSl : ∀x∈rcbW K.S K.D++rcbR K.S K.R K.E,Sl x := by decide +kernel
  have os : ∀ x∈[K.D.x,K.D.y,K.D.z], Sl x := by
    intro x hx; apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have pv : ∀ x∈[K.R.x,K.R.y,K.R.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  have qv : ∀ x∈[K.E.x,K.E.y,K.E.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd]
  apply fieldBranch_relCT hL hAl hm (pv K.R.z (by simp)) (hc.zero K.R.z (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    have hi : RelCT isa (FieldPair K.M base 8192 C.p Sl V E)
        (.block (copy K.M.n K.S.t2 K.R.x ++ copy K.M.n K.S.t4 K.R.y))
        (FieldPair K.M base 8192 C.p Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S K.R E)) := by
      apply fieldWP_relCT hc.init
      intro s hs
      exact WP.mono (jacMixedInit_ok hL hAl hSl hs hV) fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hi
    have hh : RelCT isa (FieldPair K.M base 8192 C.p Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S K.R E)) (VG.Impl.P256.VerifyAllocated.program .mixedHead)
        (FieldPair K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E))) := by
      apply fieldWP_relCT Proof.P256.VerifyAllocated.MixedHead_ct
      intro s hi
      exact WP.mono (mixedHead_ok raw hi hV) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.regs.sp⟩
    apply RelCT.seq hh
    have oldV : ∀ x∈V, x∈validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[K.D.x,K.D.y,K.D.z]++V, x∈[K.D.x,K.D.y,K.D.z]++validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (oldV x hx)
    apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
    · intro _
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
      · intro _
        have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        have hv : ∀ x∈rcbR K.S K.R K.R, x∈validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
          fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
        have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) hL hAl (callOf_small (by decide)) hm hdA hdSl hv hc.double
        exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (infinity_relCT hL hAl os hOne hc.infinity).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
    · intro _
      have ht : RelCT isa
          (FieldPair K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)))
          (VG.Impl.P256.VerifyAllocated.program .mixedTail)
          (FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
            (runOps (jacMixedHead K.S K.R K.E ++ jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E))) := by
        apply fieldWP_relCT Proof.P256.VerifyAllocated.MixedTail_ct
        intro s hi
        exact WP.mono (mixedTail_ok raw hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.regs.sp⟩
      exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)


end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `AllocatedFixedDigitTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem fixedSum_relCT (raw : RawCorrect)
    {base : Addr} {E : Nat → Fe C}
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : cfg.K.one<C.p) (hc : JointFixedChecks cfg) :
    RelCT isa (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg)
      ([cfg.K.E.x,cfg.K.E.y,cfg.K.E.z]++jointLive cfg) E)
      (.seq VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd (.block (copyPt 4 cfg.K.R cfg.K.D)))
      (fun s t => ∃ E',FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E' s t) := by
  let hL := JointLayout.fixedLayout
  have vr : ∀ x∈rcbR cfg.K.S cfg.K.R cfg.K.E,x∈[cfg.K.E.x,cfg.K.E.y,cfg.K.E.z]++jointLive cfg := by intro x hx; jslots
  apply RelCT.seq (mixedAdd_relCT raw hm vr hOne hc.mixed)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.layout.lay hL.layout.aligned
    (o:=cfg.K.R) (q:=cfg.K.D) (by decide +kernel)
    (V:=[cfg.K.D.x,cfg.K.D.y,cfg.K.D.z]++([cfg.K.E.x,cfg.K.E.y,cfg.K.E.z]++jointLive cfg))
    (by intro x hx; exact List.mem_append_left _ hx) (by rw [hL.layout.n]; exact hc.copy)
  rw [hL.layout.n] at cp
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun x hx => by simp [hx])⟩)

theorem fixedDigit_relCT (raw : RawCorrect)
    {base T : Addr} {u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hC : Law C)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hOne : cfg.K.one<C.p) (hj : j<257) (hc : JointFixedChecks cfg) :
    RelCT isa (fun s t =>
      FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A s ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Joint.fixedDigit cfg VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd)
      (fun s t => ∃ E',FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E' s t) := by
  let hL := JointLayout.fixedLayout
  have hbytes : cfg.gBits+j<8192 := by
    change 1504+j<8192
    omega
  have digit : RelCT isa (fun s t =>
      FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A s ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.digitRead cfg.G))
      (fun s t => FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A s ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 G T) A t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64 ∧ t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok (K:=cfg.G) hp.left.scr hL.gBits hbytes ps (cs.stable.generator j hj) .x2
    obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok (K:=cfg.G) hp.right.scr hL.gBits hbytes pt (ct.stable.generator j hj) .x2
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm
    have frame {a b : State} (hk : VG.Proof.Ed25519.AArch64.Keeps [.x2,.x16] a b) :
        ProgKeep cfg.K.M base [] a b := keeps_prog hk (by
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
    have sum := fun E' => fixedSum_relCT raw (base:=base) (E:=E') hm hOne hc
    exact (RelCT.seq entry (RelCT.exists_ sum)) _ _ _ _ _ _ ⟨hp,cs,ct,s19,t19,s2,t2⟩ es et
  · exact RelCT.block_nil (fun _ _ h => ⟨_,h.1.1⟩)


end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
