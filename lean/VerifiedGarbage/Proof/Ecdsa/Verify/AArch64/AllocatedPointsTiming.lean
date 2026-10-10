import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointFinishTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyExtra

/-! ## `ArithmeticTableChecks` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

private abbrev Kc := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256

/-- The forwarded blocks of the table addition are the Forward framework's
literals, so the kernel never runs the optimizer here. -/
private theorem head_lit : VG.Impl.P256.VerifyArithmetic.program Kc.M (VG.Impl.Weierstrass.jacHead Kc.S Kc.R (Naf.twice Kc)) =
    .block Forward.ArithmeticTableHead.rightCode.lit := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .tableHead) :=
    ⟨rfl,List.mem_map.mpr ⟨.tableHead,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  change VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
    (VG.Impl.P256.VerifyArithmetic.operations .tableHead) = _
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  exact congrArg Code.block Forward.ArithmeticTableHead.optimized_lit

private theorem tail_lit : VG.Impl.P256.VerifyArithmetic.program Kc.M (VG.Impl.Weierstrass.jacTail Kc.S Kc.R (Naf.twice Kc) Kc.D) =
    .block Forward.ArithmeticTableTail.rightCode.lit := by
  have hs : VG.Impl.P256.VerifyArithmetic.selected VG.Impl.P256.VerifyDouble.M
      (VG.Impl.P256.VerifyArithmetic.operations .tableTail) :=
    ⟨rfl,List.mem_map.mpr ⟨.tableTail,by simp [VG.Impl.P256.VerifyArithmetic.kinds],rfl⟩⟩
  change VG.Impl.P256.VerifyArithmetic.program VG.Impl.P256.VerifyDouble.M
    (VG.Impl.P256.VerifyArithmetic.operations .tableTail) = _
  rw [VG.Impl.P256.VerifyArithmetic.program,ite_eq_left hs]
  exact congrArg Code.block Forward.ArithmeticTableTail.optimized_lit

private theorem arithmeticTable_add_preserves : ∀ r∈[Reg.x19,Reg.x20],
    ∀ i∈instrs (ArithmeticAdd.add Kc Kc.R (Naf.twice Kc) Kc.D),dstOf i≠some r := by
  rw [ArithmeticAdd.add,head_lit,tail_lit,jacWinCfg_double_lit]
  have h : (instrs (.seq (.block (zeroMask Kc.M.n Kc.R.z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D (Naf.twice Kc))) <|
      .seq (.block (zeroMask Kc.M.n (Naf.twice Kc).z)) <|
      .ite (.nonzero .x .x2) (.block (copyPt Kc.M.n Kc.D Kc.R)) <|
      .seq (.block Forward.ArithmeticTableHead.rightCode.lit) <|
      .seq (.block (zeroMask Kc.M.n Kc.S.t3)) <|
      .ite (.nonzero .x .x2)
        (.seq (.block (zeroMask Kc.M.n Kc.S.t5)) <|
          .ite (.nonzero .x .x2) (.block Forward.P256Bounds.rightRD.lit) (.block (Jacobian.infinity Kc Kc.D)))
        (.block Forward.ArithmeticTableTail.rightCode.lit) : Prog isa)).all
      (fun i => decide (dstOf i≠some .x19 ∧ dstOf i≠some .x20))=true := by decide +kernel
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem arithmeticTable_checks : ArithmeticTableChecks (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256) where
  base := nafTable_checks
  add := {
    zero := nafTable_checks.add.zero
    copyP := nafTable_checks.add.copyP
    copyQ := nafTable_checks.add.copyQ
    head := Forward.ArithmeticTableHead.ct
    tail := Forward.ArithmeticTableTail.ct
    double := nafTable_checks.add.double
    infinity := nafTable_checks.add.infinity }
  keepAdd := arithmeticTable_add_preserves

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointPrepTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

theorem jointPrep_trace {base : Addr} :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      sv p256 base s U=sv p256 base t U ∧ sv p256 base s V=sv p256 base t V)
      jointPrepProgram (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨hs,ht,hsp,hu,hv⟩ es et
  cases es with | seq gs qs =>
    cases et with | seq gt qt =>
      have hg := (fastPrep_relCT P256Joint.cfg.G (Or.inr rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide) jointGPrep_checks
        _ _ _ _ _ _ ⟨hs,ht,hsp,hu⟩ gs gt).1
      obtain ⟨_,_,xs,ps,ks,os⟩ := fastPrep_ok P256Joint.cfg.G (Or.inr rfl) hs
        (src:=p256.sl U) (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨_,_,xt,pt,kt,ot⟩ := fastPrep_ok P256Joint.cfg.G (Or.inr rfl) ht
        (src:=p256.sl U) (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨_,rfl⟩ := Exec.det gs xs
      obtain ⟨_,rfl⟩ := Exec.det gt xt
      have vs := os.wordsVal (d:=p256.sl V) (k:=4) (by decide) (by decide)
      have vt := ot.wordsVal (d:=p256.sl V) (k:=4) (by decide) (by decide)
      have hq := (fastPrep_relCT P256Joint.cfg.K (Or.inl rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide) jointQPrep_checks
        _ _ _ _ _ _ ⟨ps.scr,pt.scr,ks.sp.trans (hsp.trans kt.sp.symm),vs.trans (hv.trans vt.symm)⟩ qs qt).1
      exact ⟨by rw [hg,hq],trivial⟩

theorem JointPrepPost.fields {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} {s t : State}
    (h : JointPrepPost base g P s t) :
    ∀ x∈winRo P256Joint.cfg.K,tmv p256.C 4 base t x=tmv p256.C 4 base s x := by
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  have e : ∀ i<45,tmv p256.C 4 base t (p256.sl i)=tmv p256.C 4 base s (p256.sl i) :=
    fun i hi => by change toM _ _ (sv p256 base t i)=toM _ _ (sv p256 base s i); rw [h.same i hi]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [e AP (by decide),e BM (by decide),e ZERO (by decide),e VG.Impl.Ecdh.AArch64.PX (by decide),e VG.Impl.Ecdh.AArch64.PY (by decide),
    e ONEP (by decide)]

/-- Shared table values and the exact public scalar digits after preparation. -/
def JointTablePair (base : Addr) (P : Point p256.C) (u v : Nat) (a b s t : State) : Prop :=
  ∃ E,FieldPair P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (nafLive P256Joint.cfg.K) E s t ∧
  ∃ g₁ g₂ a' b', JointPrepPost base g₁ P a a' ∧ JointPrepPost base g₂ P b b' ∧
    JointTablePost base g₁ P u v a' s ∧ JointTablePost base g₂ P u v b' t

theorem jointPrepTable_relCT (certs : Forward.Arithmetic.Cases) (hc : CfgOk p256) (hC : Law p256.C)
    {base : Addr} {P : Point p256.C} {u v : Nat} {a b : State} (hP : onCurve p256.C P=true) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base P v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      (.seq jointPrepProgram (ArithmeticTable.table P256Joint.cfg.K))
      (JointTablePair base P u v a b) := by
  intro s t ts tt s' t' ⟨rfl,rfl,hp,us,ut⟩ es et
  obtain ⟨g₁,fs⟩ := hp.left.fixed
  obtain ⟨g₂,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      have he := (jointPrep_trace _ _ _ _ _ _ ⟨hp.left.scr,hp.right.scr,hp.sp,
        us.trans ut.symm,hp.left.scalar.trans hp.right.scalar.symm⟩ ps pt).1
      obtain ⟨_,_,xs,is⟩ := jointPrepStage_ok hc hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it⟩ := jointPrepStage_ok hc hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have pair : FieldPair P256Joint.cfg.K.M base size p256.C.p (·∈jacWinSlots P256Joint.cfg.K)
          (winRo P256Joint.cfg.K) _ _ _ :=
        ⟨is.field,it.field.congr_env (fun x hx => (it.fields x hx).trans
          ((hp.fields x hx).symm.trans (is.fields x hx).symm)),is.keep.sp.trans (hp.sp.trans it.keep.sp.symm)⟩
      obtain ⟨hw,E,pair'⟩ := arithmeticTable_relCT certs (jacLay hc rfl) rfl (jacAligned p256 rfl)
        (unitMod_pow_two hc.p_odd _) (by decide) (by decide)
        (by change 2^(64*4)%p256.C.p<p256.C.p; exact Nat.mod_lt _ (by have := hc.p_ge; omega))
        arithmeticTable_checks nafWindow_checks.treeCopy _ _ _ _ _ _ pair ws wt
      obtain ⟨_,_,ys,js⟩ := jointTableStage_ok certs hc hC hP is
      obtain ⟨_,_,yt,jt⟩ := jointTableStage_ok certs hc hC hP it
      obtain ⟨_,rfl⟩ := Exec.det ws ys
      obtain ⟨_,rfl⟩ := Exec.det wt yt
      rw [us,hp.left.scalar] at js
      rw [ut,hp.right.scalar] at jt
      refine ⟨by rw [he,hw],E,?_,g₁,g₂,_,_,is,it,js,jt⟩
      exact ⟨⟨pair'.left.scr,pair'.left.mod,
        fun x hx => List.mem_append_left _ (List.mem_append_left _ (pair'.left.sl x hx)),pair'.left.lt,pair'.left.val⟩,
        ⟨pair'.right.scr,pair'.right.mod,
        fun x hx => List.mem_append_left _ (List.mem_append_left _ (pair'.right.sl x hx)),pair'.right.lt,pair'.right.val⟩,pair'.sp⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointGeneratorFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

theorem jointGenerator_unch {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {W : List (Nat×Nat)} (h : JointGenerator c C base size G T s)
    (hu : Unch base W s.mem t.mem) (hrd : t.rd=s.rd) (hwr : t.wr=s.wr)
    (hsym : t.syms=s.syms) (hw : ∀ w∈W,w.1+w.2≤size) :
    JointGenerator c C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<8) :
      word t.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega)
    apply hu
    intro w hm; have := hw w hm; dsimp only [off]; exact Or.inr (by omega)
  have val (a o : Nat) (ha : 1≤a) (ha32 : a≤32) (ho : o=0 ∨ o=32) :
      wordsVal t.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4=
      wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4 := by
    apply wordsVal_of_words₂
    intro i hi
    rcases ho with rfl | rfl
    · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega)
    · have e := wordeq a (4+i) ha ha32 (by omega)
      simpa only [Nat.mul_add] using e
  refine ⟨?_,?_,h.outside,?_,?_⟩
  · rw [hsym]; exact h.symbol
  · intro a ha ha32 i hi; rw [hrd,hwr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.point a ha ha32


theorem JointTablePair.generators {base T : Addr} {P G : Point p256.C} {u v : Nat}
    {a b s t : State} (h : JointTablePair base P u v a b s t)
    (ga : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T a)
    (gb : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T b) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T s ∧
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size G T t := by
  obtain ⟨_,_,_,_,_,_,pa,pb,ta,tb⟩ := h
  have ga' := jointGenerator_unch ga pa.unch pa.keep.rd pa.keep.wr pa.syms (by decide +kernel)
  have gb' := jointGenerator_unch gb pb.unch pb.keep.rd pb.keep.wr pb.syms (by decide +kernel)
  exact ⟨jointGenerator_unch ga' ta.table.unch ta.table.keep.rd ta.table.keep.wr ta.syms (by decide +kernel),
    jointGenerator_unch gb' tb.table.unch tb.table.keep.rd tb.table.keep.wr tb.syms (by decide +kernel)⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointBoundaryGenerator` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

/-- Both original table preconditions refer to the same public static table. -/
theorem jointBoundary_generators (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ s t : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀)
    (hb : JointBoundary p256 s₀ t₀ s t) :
    JointGenerator P256Joint.cfg p256.C (s₀.gpr .x3) 8192 (G p256.C) (s₀.syms p256.tsym) s ∧
    JointGenerator P256Joint.cfg p256.C (s₀.gpr .x3) 8192 (G p256.C) (s₀.syms p256.tsym) t := by
  obtain ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,_⟩ := hb
  have bs : s₀.gpr .x3=t₀.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have ls := JointGenerator.of_pre hc hC hT ps.tbl rfl
  have rt := JointGenerator.of_pre hc hC hT pt.tbl rfl
  rw [←bs,←pub.table] at rt
  exact ⟨jointGenerator_unch ls ms.unch ms.rd ms.wr ms.syms (by simp),
    jointGenerator_unch rt mt.unch mt.rd mt.wr mt.syms (by simp)⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointInputTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdh.AArch64 Spec.Weierstrass

/-- The original public verifier relation determines both joint scalars and the peer. -/
theorem jointBoundary_input (hc : CfgOk p256) (hC : Law p256.C)
    {s₀ t₀ s t : State} (h : JointBoundary p256 s₀ t₀ s t) :
    JacWinPublic p256 (s₀.gpr .x3)
      (peerPt p256 (s₀.mem (s₀.gpr .x0)=4) (keyX p256 s₀) (keyY p256 s₀))
      (publicV p256 s₀) s t ∧
    sv p256 (s₀.gpr .x3) s U=publicU p256 s₀ ∧
    sv p256 (s₀.gpr .x3) t U=publicU p256 s₀ := by
  obtain ⟨pub,⟨g₁,m₁⟩,⟨g₂,m₂⟩,sp⟩ := h
  have peer := mid_peer_public pub m₁ m₂
  refine ⟨⟨⟨m₁.scr,⟨g₁,m₁.fixed⟩,m₁.px_lt,m₁.py_lt,m₁.peer_rep hc hC,mid_publicV m₁⟩,
    ⟨m₂.scr,⟨g₂,m₂.fixed⟩,m₂.px_lt,m₂.py_lt,?_,(mid_publicV m₂).trans pub.v.symm⟩,
    sp,peer.1,peer.2⟩,mid_publicU m₁,(mid_publicU m₂).trans pub.u.symm⟩
  rw [pub.peerPoint]
  exact m₂.peer_rep hc hC

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointPointsTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open P256Joint

theorem jointAfterTable_relCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (JointTablePair base Q u v a b)
      (.seq (CachedJac.cache cfg.K)
        (.seq (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
          (.seq (Joint.run cfg ops) (Jacobian.jacFinish cfg.K))))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hm : UnitMod p256.C.p (2^(64*cfg.K.M.n)) := unitMod_pow_two hc.p_odd _
  have one : cfg.K.one<p256.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have cache : RelCT isa (JointTablePair base Q u v a b) (CachedJac.cache cfg.K)
      (JointCachePair p256.C base T P Q u v) := by
    intro s t ts tt s' t' h es et
    have ⟨gs,gt⟩ := h.generators ga gb
    obtain ⟨E,hp,_,_,_,_,_,_,ps,pt⟩ := h
    exact jointCache_relCT hm _ _ _ _ _ _
      ⟨hp,ps.stable,pt.stable,ps.generator,pt.generator,ps.one,pt.one,gs,gt⟩ es et
  apply RelCT.seq cache
  apply RelCT.seq (jointInit_relCT one)
  exact RelCT.seq (jointRun_timing hm hC hc.am3 one hP hQ hu hv) (jointFinish_relCT hc hC)

theorem jointPoints_inputCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base Q v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      P256Joint.points (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  change RelCT isa _ (.seq _ (.seq _ (.seq _ _))) _
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (jointPrepTable_relCT Forward.Arithmetic.cases hc hC hQ)
    (jointAfterTable_relCT hc hC hP hQ hu hv ga gb)

/-- The complete joint points stage depends only on the original public inputs. -/
theorem jointPoints_relCT (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) P256Joint.points
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hb es et
  obtain ⟨hp,us,ut⟩ := jointBoundary_input hc hC hb
  obtain ⟨gs,gt⟩ := jointBoundary_generators hc hC hT ps pt hb
  have hu : publicU p256 s₀<2^256 := by
    rw [←us]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl U) 4
  have hv : publicV p256 s₀<2^256 := by
    rw [←hp.left.scalar]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl V) 4
  exact jointPoints_inputCT hc hC hc.onG (peerPt_onCurve hc _ _ _) hu hv gs gt
    _ _ _ _ _ _ ⟨rfl,rfl,hp,us,ut⟩ es et

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedPointsTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem allocatedAfterTable_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (JointTablePair base Q u v a b)
      (.seq (CachedJac.cache cfg.K)
        (.seq (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
          (.seq (Joint.run cfg P256Allocated.ops) (Jacobian.jacFinish cfg.K))))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hm : UnitMod p256.C.p (2^(64*cfg.K.M.n)) := unitMod_pow_two hc.p_odd _
  have one : cfg.K.one<p256.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have cache : RelCT isa (JointTablePair base Q u v a b) (CachedJac.cache cfg.K)
      (JointCachePair p256.C base T P Q u v) := by
    intro s t ts tt s' t' h es et
    have ⟨gs,gt⟩ := h.generators ga gb
    obtain ⟨E,hp,_,_,_,_,_,_,ps,pt⟩ := h
    exact jointCache_relCT hm _ _ _ _ _ _
      ⟨hp,ps.stable,pt.stable,ps.generator,pt.generator,ps.one,pt.one,gs,gt⟩ es et
  apply RelCT.seq cache
  apply RelCT.seq (jointInit_relCT one)
  exact RelCT.seq (allocatedRun_timing raw hm hC hc.am3 one hP hQ hu hv) (jointFinish_relCT hc hC)

theorem allocatedPoints_inputCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base Q v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V)) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  change RelCT isa _ (.seq _ (.seq _ (.seq _ _))) _
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (jointPrepTable_relCT Forward.Arithmetic.cases hc hC hQ)
    (allocatedAfterTable_relCT raw hc hC hP hQ hu hv ga gb)

theorem allocatedPointsBody_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hb es et
  obtain ⟨hp,us,ut⟩ := jointBoundary_input hc hC hb
  obtain ⟨gs,gt⟩ := jointBoundary_generators hc hC hT ps pt hb
  have hu : publicU p256 s₀<2^256 := by
    rw [←us]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl U) 4
  have hv : publicV p256 s₀<2^256 := by
    rw [←hp.left.scalar]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl V) 4
  exact allocatedPoints_inputCT raw hc hC hc.onG (peerPt_onCurve hc _ _ _) hu hv gs gt
    _ _ _ _ _ _ ⟨rfl,rfl,hp,us,ut⟩ es et


private theorem saveBoundary_relCT {s₀ t₀ : State} :
    RelCT isa (JointBoundary p256 s₀ t₀) (.block P256Allocated.saveExtra)
      (JointBoundary p256 s₀ t₀) := by
  intro s t ts tt s' t' ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,sp⟩ es et
  obtain ⟨_,_,xs,ks,us,_⟩ := allocatedSave_ok ms.scr (by decide)
  obtain ⟨_,_,xt,kt,ut,_⟩ := allocatedSave_ok mt.scr (by decide)
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have hp : AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
    refine ⟨sp,fun r hr => ?_⟩
    have : r=.x0 := by simpa only [Taint.mem_ofRegs,List.mem_singleton] using hr
    subst r
    exact ms.scr.x0.trans mt.scr.x0.symm
  exact ⟨invAllocated_save_ct _ _ _ _ _ _ trivial trivial hp es et,
    pub,⟨gs,mid_saved ms ks us (Exec.syms es)⟩,⟨gt,mid_saved mt kt ut (Exec.syms et)⟩,
    ks.sp.trans (sp.trans kt.sp.symm)⟩

private theorem restorePublic_relCT :
    RelCT isa (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block P256Allocated.restoreExtra)
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  refine ⟨invAllocated_restore_ct _ _ _ _ _ _ trivial trivial hp es et,
    (Exec.rdwr es).2.2.trans (hp.1.trans (Exec.rdwr et).2.2.symm),fun r hr => ?_⟩
  have : r=.x0 := by simpa only [Taint.mem_ofRegs,List.mem_singleton] using hr
  subst r
  have keep : ∀i∈instrs (.block P256Allocated.restoreExtra : Prog isa),dstOf i≠some .x0 := by decide
  rw [Exec.gpr keep es,Exec.gpr keep et]
  exact hp.2 _ (by decide)

/-- The allocated points stage preserves the original public-input timing contract,
including the save and restore of its extra working registers. -/
theorem allocatedPoints_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) P256Allocated.points
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  rw [P256Allocated.points]
  exact RelCT.seq saveBoundary_relCT
    (RelCT.seq (allocatedPointsBody_relCT raw hc hC hT ps pt) restorePublic_relCT)

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
