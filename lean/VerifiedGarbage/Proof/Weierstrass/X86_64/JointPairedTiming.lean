module

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit

/-! Attach the functional invariant to paired field execution at each stage. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def JointPair (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Core : Point C → State → Prop) (A : Point C) (j : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t) ∧
    Core A s ∧ Core A t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j

theorem jointPair_stage {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A B : Point C} {code : Prog isa} {W : List Nat}
    (hw : ∀ s,Core A s → s.gpr .rbx=BitVec.ofNat 64 j →
      WP isa code.inline s fun t => ProgKeep c.K.M base W s t ∧ Core B t)
    (ht : ∀ E,RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      Core A s ∧ Core A t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      code.inline (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)) :
    RelCT isa (JointPair c C base size Core A j) code.inline (JointPair c C base size Core B j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨he,hp'⟩ := ht E _ _ _ _ _ _ ⟨hp,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,ks,cs'⟩ := hw s cs ps
  obtain ⟨_,_,xt,kt,ct'⟩ := hw t ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,hp',cs',ct',(ks.gpr _ (rbx_not_clob _)).trans ps,
    (kt.gpr _ (rbx_not_clob _)).trans pt⟩

structure JointOpsTiming (c : Joint.Cfg) (double : Prog isa) (C : Curve) (base : Addr)
    (size : Nat) (Core : Point C → State → Prop) : Prop where
  double : ∀ A j E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
    double.inline (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  peer : ∀ A j,j<64*c.K.M.n+1 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
    (Joint.cachedDigit c).inline (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  generator : ∀ A j,j<64*c.K.M.n+1 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
    (Joint.fixedDigit c).inline (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)

theorem jointCounterCT : RegCT [.rbx] (.block [.alu .sub .rbx (.imm 1)]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem jointTestCT : RegCT [.rbx] (.block [.alu .test .rbx (.reg .rbx)]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem jointPair_counter {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,Keeps [.rbx] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j+1<2^64) :
    RelCT isa (JointPair c C base size Core A (j+1)) (.block [.alu .sub .rbx (.imm 1)])
      (JointPair c C base size Core A j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,sb,ks⟩ := decRbx_ok s (by omega) (by omega) ps
  obtain ⟨_,_,xt,tb,kt⟩ := decRbx_ok t (by omega) (by omega) pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have he : ts=tt := jointCounterCT _ _ _ _ _ _ trivial trivial
    (Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm)) es et
  refine ⟨he,⟨E,hp.1.of_keeps ks (by decide),hp.2.of_keeps kt (by decide)⟩,
    hkeep A _ _ ks (Exec.syms es) cs,hkeep A _ _ kt (Exec.syms et) ct,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using sb
  · simpa only [Nat.add_sub_cancel] using tb

theorem jointPair_test {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,Keeps [] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j<2^64) :
    RelCT isa (JointPair c C base size Core A j) (.block [.alu .test .rbx (.reg .rbx)])
      (fun s t => JointPair c C base size Core A j s t ∧
        s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0))) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,sz,ks⟩ := testRbx_ok s (by omega) ps
  obtain ⟨_,_,xt,tz,kt⟩ := testRbx_ok t (by omega) pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have he : ts=tt := jointTestCT _ _ _ _ _ _ trivial trivial
    (Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm)) es et
  exact ⟨he,⟨⟨E,hp.1.of_keeps ks (by decide),hp.2.of_keeps kt (by decide)⟩,
    hkeep A _ _ ks (Exec.syms es) cs,hkeep A _ _ kt (Exec.syms et) ct,
    (ks.1 _ (by simp)).trans ps,(kt.1 _ (by simp)).trans pt⟩,sz,tz⟩

/-- `cmp rbx, k` reads only `rbx` (its immediate erased for the analysis). -/
theorem jointCmpCT (k : BitVec 32) : RegCT [.rbx] (.block [.alu .cmp .rbx (.imm k)]) :=
  VG.Taint.constantTime_mapBlocks (c' := .block [.alu .cmp .rbx (.imm 0)]) taintS_eraseInv
    (Taint.ofRegs [.rbx]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

theorem jointPair_cmp {c : Joint.Cfg} {C : Curve} {base : Addr} {size j k : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,Keeps [] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j<2^64) (hk : k<2^31) :
    RelCT isa (JointPair c C base size Core A j) (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))])
      (fun s t => JointPair c C base size Core A j s t ∧
        s.zf=some (decide (j=k)) ∧ t.zf=some (decide (j=k))) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,sz,ks⟩ := cmpRbxImm_ok s hj hk ps
  obtain ⟨_,_,xt,tz,kt⟩ := cmpRbxImm_ok t hj hk pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have he : ts=tt := jointCmpCT _ _ _ _ _ _ _ trivial trivial
    (Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm)) es et
  exact ⟨he,⟨⟨E,hp.1.of_keeps ks (by decide),hp.2.of_keeps kt (by decide)⟩,
    hkeep A _ _ ks (Exec.syms es) cs,hkeep A _ _ kt (Exec.syms et) ct,
    (ks.1 _ (by simp)).trans ps,(kt.1 _ (by simp)).trans pt⟩,sz,tz⟩

/-- No code. -/
theorem relCT_nil {P Q : State → State → Prop} (h : ∀ s t,P s t → Q s t) : RelCT isa P (.block []) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rfl,rfl⟩ := Exec.det e₁ (Exec.block rfl)
  obtain ⟨rfl,rfl⟩ := Exec.det e₂ (Exec.block rfl)
  exact ⟨rfl,h _ _ hp⟩

section
variable {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {double : Prog isa}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
    (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)


variable (ht : JointOpsTiming c double C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)))
    (hdouble : ∀ A s,onCurve C A=true → (JointCore c C base size Q u v (JointGenerator c C base T size row)) A s →
      WP isa double.inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧ (JointCore c C base size Q u v (JointGenerator c C base T size row)) (add A A) t)

include hL hm hC ha hOne hOneVal hG hQ ht

theorem jointPair_digits {j : Nat} {A : Point C} (hA : onCurve C A=true) (hj : j<64*c.K.M.n+1) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) A j) (Joint.digits c).inline
      (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C G c.gw u j)) j) := by
  apply RelCT.seq (jointPair_stage (fun s hs hb => jointCachedDigit_ok hL hm hC ha hOne hQ hA hs
    (JointGenerator.workKeep hL.lookup.layout hs.field.mod.tmp) hj hb) (ht.peer A j hj))
  exact jointPair_stage (fun s hs hb => jointFixedDigit_ok hL hm hC ha hOne hOneVal hG
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) hs hj hb) (ht.generator _ j hj)

include hdouble

omit hm hC ha hOne hOneVal hG hQ in
/-- The doubling but where `R` is `O`, in the first iteration (`j = 64 n`). -/
theorem jointPair_guard {j : Nat} {A : Point C} (hA : onCurve C A=true) (hj : j<Joint.top c)
    (h0 : j=64*c.K.M.n → add A A=A) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) A j)
      (Joint.guardDouble c double).inline
      (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (add A A) j) := by
  have hk (rs : List Reg) (hr : Reg.rdi∉rs) (A : Point C) (s t : State)
      (ks : Keeps rs s t) (st : t.syms=s.syms) (cs : (JointCore c C base size Q u v (JointGenerator c C base T size row)) A s) : (JointCore c C base size Q u v (JointGenerator c C base T size row)) A t :=
    cs.of_keeps ks hr (fun n hn hb ho => (cs.external n hn hb ho).of_keeps ks st)
  have := hL.lookup.layout.n
  have := joint_top_le c
  rw [Joint.guardDouble]
  split
  · exact (jointPair_stage (fun s hs _ => hdouble _ s hA hs) (ht.double _ j)).mono
      (fun _ _ h => h) (fun _ _ h => h)
  simp only [Code.inline]
  apply RelCT.seq (jointPair_cmp (k:=64*c.K.M.n) (hk [] (by simp)) (by omega) (by omega))
  refine RelCT.ite (fun s t h => by show s.zf=t.zf; rw [h.2.1,h.2.2]) ?_ ?_
  · refine relCT_nil fun s t ⟨⟨p,zs,_⟩,he⟩ => ?_
    have hz : s.zf=some true := he
    rw [zs] at hz
    rw [h0 (by simpa using hz)]
    exact p
  · exact (jointPair_stage (fun s hs _ => hdouble _ s hA hs) (ht.double _ j)).mono
      (fun _ _ h => h.1.1) (fun _ _ h => h)

theorem jointPair_step (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) {j : Nat} (hj : j<Joint.top c) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (jointPoint G Q u v (j+1) c.gw) (j+1))
      (Joint.step c double).inline (fun s t => JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (jointPoint G Q u v j c.gw) j s t ∧
        s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0))) := by
  have hk (rs : List Reg) (hr : Reg.rdi∉rs) (A : Point C) (s t : State)
      (ks : Keeps rs s t) (st : t.syms=s.syms) (cs : (JointCore c C base size Q u v (JointGenerator c C base T size row)) A s) : (JointCore c C base size Q u v (JointGenerator c C base T size row)) A t :=
    cs.of_keeps ks hr (fun n hn hb ho => (cs.external n hn hb ho).of_keeps ks st)
  have hA := jointPoint_curve hC hG hQ u v (j+1) c.gw
  have := hL.lookup.layout.n
  have := joint_top_le c
  apply RelCT.seq (jointPair_counter (hk [.rbx] (by decide)) (by omega))
  apply RelCT.seq (jointPair_guard hL ht hdouble hA hj
    (fun h => by rw [h, jointPoint_topB G Q hu hv c.gw]; rfl))
  apply RelCT.seq
  · simpa only [jointPoint_step hC hG hQ (gw:=c.gw)] using
      jointPair_digits hL hm hC ha hOne hOneVal hG hQ ht (hC.onCurve_add hA hA)
        (by omega : j<64*c.K.M.n+1)
  · exact jointPair_test (j:=j) (hk [] (by simp)) (by omega)

theorem jointPair_run (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (Joint.top c)) (Joint.run c double).inline
      (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (add (mul u G) (mul v Q)) 0) := by
  have := hL.lookup.layout.n
  have he := jointPoint_step hC hG hQ u v (64*c.K.M.n) c.gw
  rw [jointPoint_topB G Q hu hv c.gw] at he
  change add (add .infinity (FastNaf.point C Q 5 v (64*c.K.M.n)))
    (FastNaf.point C G c.gw u (64*c.K.M.n))=jointPoint G Q u v (64*c.K.M.n) c.gw at he
  have out := jointRun_relCT (c:=c) (double:=double) (by omega)
    (Pre:=JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (Joint.top c))
    (fun j => JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (jointPoint G Q u v j c.gw) j)
    (fun hp => by
      have seed := jointPair_digits (base:=base) (T:=T) (u:=u) (v:=v) (row:=row) (j:=64*c.K.M.n)
        (A:=.infinity) hL hm hC ha hOne hOneVal hG hQ ht rfl (by omega)
      rw [he] at seed
      simpa only [joint_top_peel hp] using seed)
    (fun hp s t h => by
      simpa only [joint_top_guard hp,jointPoint_topB G Q hu hv c.gw] using h)
    (fun j hj => jointPair_step hL hm hC ha hOne hOneVal hG hQ ht hdouble hu hv hj)
  simpa only [jointPoint_zero (gw:=c.gw)] using out
end
end VG.Proof.Weierstrass.X86_64
