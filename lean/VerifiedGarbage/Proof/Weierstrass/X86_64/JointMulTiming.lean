module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafLayout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! ### `Weierstrass.X86_64.JointPairedTiming`, which this module and modules that import it used -/

section

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
  obtain ⟨_,_,xs,sb,ks⟩ := decRbx_ok s (by omega_using []) (by omega_using [hj]) ps
  obtain ⟨_,_,xt,tb,kt⟩ := decRbx_ok t (by omega_using []) (by omega_using [hj]) pt
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
  obtain ⟨_,_,xs,sz,ks⟩ := testRbx_ok s (by omega_using [hj]) ps
  obtain ⟨_,_,xt,tz,kt⟩ := testRbx_ok t (by omega_using [hj]) pt
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
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p)
    (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)


variable (ht : JointOpsTiming c double C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)))
    (hdouble : ∀ A s,onCurve C A=true → (JointCore c C base size Q u v (JointGenerator c C base T size row)) A s →
      WP isa double.inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧ (JointCore c C base size Q u v (JointGenerator c C base T size row)) (add A A) t)

include hL hm hC hd hOne hOneVal hG hQ ht

theorem jointPair_digits {j : Nat} {A : Point C} (hA : onCurve C A=true) (hj : j<64*c.K.M.n+1) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) A j) (Joint.digits c).inline
      (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C G c.gw u j)) j) := by
  apply RelCT.seq (jointPair_stage (fun s hs hb => jointCachedDigit_ok hL hm hC hd hOne hQ hA hs
    (JointGenerator.workKeep hL.lookup.layout hs.field.mod.tmp) hj hb) (ht.peer A j hj))
  exact jointPair_stage (fun s hs hb => jointFixedDigit_ok hL hm hC hd hOne hOneVal hG
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) hs hj hb) (ht.generator _ j hj)

include hdouble

omit hm hC hd hOne hOneVal hG hQ in
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
  apply RelCT.seq (jointPair_cmp (k:=64*c.K.M.n) (hk [] (by simp)) (by omega_arith) (by omega_arith))
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
  apply RelCT.seq (jointPair_counter (hk [.rbx] (by decide)) (by omega_arith))
  apply RelCT.seq (jointPair_guard hL ht hdouble hA hj
    (fun h => by rw [h, jointPoint_topB G Q hu hv c.gw]; rfl))
  apply RelCT.seq
  · simpa only [jointPoint_step hC hG hQ (gw:=c.gw)] using
      jointPair_digits hL hm hC hd hOne hOneVal hG hQ ht (hC.onCurve_add hA hA)
        (by omega_using [hj, this] : j<64*c.K.M.n+1)
  · exact jointPair_test (j:=j) (hk [] (by simp)) (by omega_arith)

theorem jointPair_run (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (Joint.top c)) (Joint.run c double).inline
      (JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (add (mul u G) (mul v Q)) 0) := by
  have := hL.lookup.layout.n
  have he := jointPoint_step hC hG hQ u v (64*c.K.M.n) c.gw
  rw [jointPoint_topB G Q hu hv c.gw] at he
  change add (add .infinity (FastNaf.point C Q 5 v (64*c.K.M.n)))
    (FastNaf.point C G c.gw u (64*c.K.M.n))=jointPoint G Q u v (64*c.K.M.n) c.gw at he
  have out := jointRun_relCT (c:=c) (double:=double) (by omega_using [this])
    (Pre:=JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (Joint.top c))
    (fun j => JointPair c C base size (JointCore c C base size Q u v (JointGenerator c C base T size row)) (jointPoint G Q u v j c.gw) j)
    (fun hp => by
      have seed := jointPair_digits (base:=base) (T:=T) (u:=u) (v:=v) (row:=row) (j:=64*c.K.M.n)
        (A:=.infinity) hL hm hC hd hOne hOneVal hG hQ ht rfl (by omega_using [])
      rw [he] at seed
      simpa only [joint_top_peel hp] using seed)
    (fun hp s t h => by
      simpa only [joint_top_guard hp,jointPoint_topB G Q hu hv c.gw] using h)
    (fun j hj => jointPair_step hL hm hC hd hOne hOneVal hG hQ ht hdouble hu hv hj)
  simpa only [jointPoint_zero (gw:=c.gw)] using out
end
end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The joint two-scalar multiplication: timing

Two runs from equal public scalars and field inputs take the same branches
and addresses: the joint multiplication of `JointMul.lean` with the curve's
doubler (`JointDoubler.ct`), given the taint checks of its parts.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open Spec.Weierstrass

theorem jointMulOps_timing {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hds : JDblShape c.dbl) (hD : JointDoubler c C size double) :
    JointOpsTiming c double C base size
      (JointCore c C base size Q u v (JointGenerator c C base T size row)) := by
  constructor
  · intro A j E
    exact hD.ct.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · intro A j hj E
    exact jointCachedDigit_relCT hL hm hOne hj hc hds
      (fun _ _ hk st hs a ha hb ho => (hs a ha hb ho).of_keeps hk st)
  · intro A j hj E
    exact jointFixedDigit_relCT hL hm hOne hj hf hds

theorem jointMulRun_relCT {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (JointPair c C base size
      (JointCore c C base size Q u v (JointGenerator c C base T size row)) .infinity (Joint.top c))
      (Joint.run c double).inline
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) :=
  jointPair_run hL hm hC hd hOne hOneVal hG hQ (jointMulOps_timing hL hm hOne hc hf hd.shape hD)
    (fun _ _ hp hi => hD.ok (JointGenerator.workKeep hL.lookup.layout hi.field.mod.tmp) hp hi) hu hv

theorem jointMulWindow_relCT {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {E : Nat → Fin C.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hd : JDblOk C c.dbl) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hZ : c.coZ=true → PrimeOrder C ∧ 17≤C.n ∧ AM3 C)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (ht : JointTableChecks c) (hcache : ScratchCT (Joint.cacheCode c).inline)
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))]))
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t)
      (Joint.window c double).inline
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) := by
  let Init := fun s => Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c)
      (tmv C c.K.M.n base s) s ∧ JointStable c C base Q u v s ∧
      JointGenerator c C base T size row s
  have table := (jointTables_relCT (C:=C) (base:=base) (E:=E) hInit hm hOne ht hd.shape hcache).mono
    (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t)
    (fun s t h => h.1) (fun s t h => h)
  have table' := table.wp (F₁:=Init) (F₂:=Init) (fun s t ⟨hp,ps,pt⟩ =>
    ⟨WP.mono (jointTables_ok hInit hm hC hd hOne hQ hp.1.to_tmv ps.point ps.affine hZ ps.zero ps.peer ps.generator ps.external)
      (fun _ h => h.2),
     WP.mono (jointTables_ok hInit hm hC hd hOne hQ hp.2.to_tmv pt.point pt.affine hZ pt.zero pt.peer pt.generator pt.external)
      (fun _ h => h.2)⟩)
  rw [Joint.window]
  simp only [Code.inline]
  apply RelCT.assoc
  apply RelCT.seq (table'.mono
    (Q':=fun (s t : State) => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
    (fun _ _ h => h)
    (fun _ _ ⟨⟨E',hp⟩,ps,pt⟩ => ⟨E',hp,ps,pt⟩))
  apply RelCT.seq (R:=JointPair c C base size
    (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (Joint.top c))
  · apply RelCT.exists_
    intro E'
    have seed := (jointSeed_relCT (C:=C) (base:=base) (E:=E') hL.lookup.layout hOne hseed hctr).mono
      (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
      (fun s t h => h.1) (fun s t h => h)
    have seed' := seed.wp (fun s t ⟨_,ps,pt⟩ =>
      ⟨WP.mono (jointSeed_ok hL.lookup.layout hOne ps.1 ps.2.1 ps.2.2) (fun _ h => h.2),
       WP.mono (jointSeed_ok hL.lookup.layout hOne pt.1 pt.2.1 pt.2.2) (fun _ h => h.2)⟩)
    exact seed'.mono (fun _ _ h => h) (fun _ _ ⟨hp,ps,pt⟩ => ⟨⟨_,hp⟩,ps.1,pt.1,ps.2,pt.2⟩)
  · exact jointMulRun_relCT hL hm hC hd hD hOne hOneVal hG hQ hc hf hu hv

/-- Any code with the recoders' timing that leaves what they leave (`JointPrepPost`). -/
theorem jointMulPrepOf_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {E : Nat → Fin C.p}
    {p : Prog isa}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hp1 : E c.K.P.z=1) (hz : E c.K.zero=0)
    (hct : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base srcU c.K.M.n=wordsVal t.mem base srcU c.K.M.n ∧
      wordsVal s.mem base srcV c.K.M.n=wordsVal t.mem base srcV c.K.M.n) p (fun _ _ => True))
    (hP : ∀ s : State,Scr s base size → WP isa p s (JointPrepPost c base size srcU srcV s)) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
      p
      (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
        JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t) := by
  have ct := hct.mono
    (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
    (fun _ _ ⟨p,_,_,su,sv,tu,tv⟩ => ⟨p.1.scr,p.2.scr,su.trans tu.symm,sv.trans tv.symm⟩)
    (fun _ _ h => h)
  let Post := fun (s : State) => Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s ∧
    JointWindowInput c C base T size u v Q row s
  exact (ct.wp (F₁:=Post) (F₂:=Post) (fun s t ⟨p,gs,gt,su,sv,tu,tv⟩ =>
    ⟨WP.mono (jointMulPrepOf_ok hL hF p.1 hp hp1 hz gs su sv (hP s p.1.scr)) (fun _ h => ⟨h.1,h.2.1⟩),
     WP.mono (jointMulPrepOf_ok hL hF p.2 hp hp1 hz gt tu tv (hP t p.2.scr)) (fun _ h => ⟨h.1,h.2.1⟩)⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_,ps,pt⟩ => ⟨⟨ps.1,pt.1⟩,ps.2,pt.2⟩)

theorem jointMulPrep_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {E : Nat → Fin C.p}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hp1 : E c.K.P.z=1) (hz : E c.K.zero=0)
    (hcG : JointPrepGChecks c srcU) (hcQ : JointPrepQChecks c srcV) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
      (Joint.prep c srcU srcV)
      (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
        JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t) :=
  jointMulPrepOf_relCT hL hF hp hp1 hz
    (jointPrep_relCT (base:=base) hL.n hL.sourceU hL.sourceV hL.generator hL.peer hL.keepV hL.recode hcG hcQ)
    (fun _ hs => jointPrep_ok hL.n hs hL.sourceU hL.sourceV hL.generator hL.peer hL.separate hL.keepV hL.recode)

theorem jointMul_relCT {C : Curve} {c : Joint.Cfg} {double : Prog isa} {base T : Addr}
    {size srcU srcV u v : Nat} {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)}
    {E : Nat → Fin C.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hPrep : JointPrepLayout c size srcU srcV)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hd : JDblOk C c.dbl)
    (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hp1 : E c.K.P.z=1) (hz : E c.K.zero=0)
    (hZ : c.coZ=true → PrimeOrder C ∧ 17≤C.n ∧ AM3 C)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (ht : JointTableChecks c) (hcache : ScratchCT (Joint.cacheCode c).inline)
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))]))
    (hcG : JointPrepGChecks c srcU) (hcQ : JointPrepQChecks c srcV) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
      (Code.seq (Joint.prep c srcU srcV) (Joint.window c double)).inline
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) := by
  show RelCT isa _ (.seq (Joint.prep c srcU srcV).inline (Joint.window c double).inline) _
  rw [jointPrep_inline]
  exact RelCT.seq (jointMulPrep_relCT hPrep hInit.naf.lay hp hp1 hz hcG hcQ)
    (jointMulWindow_relCT hL hInit hm hC hd hD hOne hOneVal hG hQ hZ hc hf ht hcache hseed hctr hu hv)

end VG.Proof.Weierstrass.X86_64
