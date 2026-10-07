import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming

/-!
# The joint two-scalar multiplication: timing

Two runs from equal public scalars and field inputs take the same branches
and addresses: the joint multiplication of `JointMul.lean` with the curve's
doubler (`JointDoubler.ct`), given the taint checks of its parts.
-/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open Spec.Weierstrass

theorem jointMulOps_timing {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hD : JointDoubler c C size double) :
    JointOpsTiming c double C base size
      (JointCore c C base size Q u v (JointGenerator c C base T size row)) := by
  constructor
  · intro A j E
    exact hD.ct.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · intro A j hj E
    exact jointCachedDigit_relCT hL hm hOne hj hc
      (fun _ _ hk st hs a ha hb ho => (hs a ha hb ho).of_keeps hk st)
  · intro A j hj E
    exact jointFixedDigit_relCT hL hm hOne hj hf

theorem jointMulRun_relCT {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (JointPair c C base size
      (JointCore c C base size Q u v (JointGenerator c C base T size row)) .infinity (64*c.K.M.n))
      (Joint.run c double)
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) :=
  jointPair_run hL hm hC ha hOne hOneVal hG hQ (jointMulOps_timing hL hm hOne hc hf hD)
    (fun _ _ hp hi => hD.ok (JointGenerator.workKeep hL.lookup.layout hi.field.mod.tmp) hp hi) hu hv

theorem jointMulWindow_relCT {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G} {E : Nat → Fin C.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (ht : NafTableChecks c.K) (hcache : ScratchCT (Naf.cacheTable c.K.M c.K.tbl c.cache 8))
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*c.K.M.n)))]))
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t)
      (Joint.window c double)
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) := by
  let Init := fun s => Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c)
      (tmv C c.K.M.n base s) s ∧ JointStable c C base Q u v s ∧
      JointGenerator c C base T size row s
  have table := (jointTables_relCT (C:=C) (base:=base) (E:=E) hInit hm hOne ht hcache).mono
    (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t)
    (fun s t h => h.1) (fun s t h => h)
  have table' := table.wp (F₁:=Init) (F₂:=Init) (fun s t ⟨hp,ps,pt⟩ =>
    ⟨WP.mono (jointTables_ok hInit hm hC ha hOne hQ hp.1.to_tmv ps.point ps.zero ps.peer ps.generator ps.external)
      (fun _ h => h.2),
     WP.mono (jointTables_ok hInit hm hC ha hOne hQ hp.2.to_tmv pt.point pt.zero pt.peer pt.generator pt.external)
      (fun _ h => h.2)⟩)
  rw [Joint.window]
  apply RelCT.assoc
  apply RelCT.seq (table'.mono
    (Q':=fun (s t : State) => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
    (fun _ _ h => h)
    (fun _ _ ⟨⟨E',hp⟩,ps,pt⟩ => ⟨E',hp,ps,pt⟩))
  apply RelCT.seq (R:=JointPair c C base size
    (JointCore c C base size Q u v (JointGenerator c C base T size row))
      .infinity (64*c.K.M.n))
  · apply RelCT.exists_
    intro E'
    have seed := (jointSeed_relCT (C:=C) (base:=base) (E:=E') hL.lookup.layout hOne hseed hctr).mono
      (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
      (fun s t h => h.1) (fun s t h => h)
    have seed' := seed.wp (fun s t ⟨_,ps,pt⟩ =>
      ⟨WP.mono (jointSeed_ok hL.lookup.layout hOne ps.1 ps.2.1 ps.2.2) (fun _ h => h.2),
       WP.mono (jointSeed_ok hL.lookup.layout hOne pt.1 pt.2.1 pt.2.2) (fun _ h => h.2)⟩)
    exact seed'.mono (fun _ _ h => h) (fun _ _ ⟨hp,ps,pt⟩ => ⟨⟨_,hp⟩,ps.1,pt.1,ps.2,pt.2⟩)
  · exact jointMulRun_relCT hL hm hC ha hD hOne hOneVal hG hQ hc hf hu hv

theorem jointMulPrep_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G} {E : Nat → Fin C.p}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hz : E c.K.zero=0)
    (hcG : FastPrepChecks c.K.M.n srcU c.gBits 7) (hcQ : FastPrepChecks c.K.M.n srcV c.K.bits 5) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
      (Joint.prep c srcU srcV)
      (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
        JointWindowInput c C base T size u v Q row s ∧ JointWindowInput c C base T size u v Q row t) := by
  have ct := (jointPrep_relCT (base:=base) hL.n hL.sourceU hL.sourceV hL.generator hL.peer hL.keepV hcG hcQ).mono
    (P':=fun (s t : State) => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
    (fun _ _ ⟨p,_,_,su,sv,tu,tv⟩ => ⟨p.1.scr,p.2.scr,su.trans tu.symm,sv.trans tv.symm⟩)
    (fun _ _ h => h)
  let Post := fun (s : State) => Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s ∧
    JointWindowInput c C base T size u v Q row s
  exact (ct.wp (F₁:=Post) (F₂:=Post) (fun s t ⟨p,gs,gt,su,sv,tu,tv⟩ =>
    ⟨WP.mono (jointMulPrep_ok hL hF p.1 hp hz gs su sv) (fun _ h => ⟨h.1,h.2.1⟩),
     WP.mono (jointMulPrep_ok hL hF p.2 hp hz gt tu tv) (fun _ h => ⟨h.1,h.2.1⟩)⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_,ps,pt⟩ => ⟨⟨ps.1,pt.1⟩,ps.2,pt.2⟩)

theorem jointMul_relCT {C : Curve} {c : Joint.Cfg} {double : Prog isa} {base T : Addr}
    {size srcU srcV u v : Nat} {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    {E : Nat → Fin C.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hPrep : JointPrepLayout c size srcU srcV)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hz : E c.K.zero=0)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (ht : NafTableChecks c.K) (hcache : ScratchCT (Naf.cacheTable c.K.M c.K.tbl c.cache 8))
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*c.K.M.n)))]))
    (hcG : FastPrepChecks c.K.M.n srcU c.gBits 7) (hcQ : FastPrepChecks c.K.M.n srcV c.K.bits 5) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c C base T size row s ∧ JointGenerator c C base T size row t ∧
      wordsVal s.mem base srcU c.K.M.n=u ∧ wordsVal s.mem base srcV c.K.M.n=v ∧
      wordsVal t.mem base srcU c.K.M.n=u ∧ wordsVal t.mem base srcV c.K.M.n=v)
      (.seq (Joint.prep c srcU srcV) (Joint.window c double))
      (JointPair c C base size
        (JointCore c C base size Q u v (JointGenerator c C base T size row))
        (add (mul u G) (mul v Q)) 0) :=
  RelCT.seq (jointMulPrep_relCT hPrep hInit.naf.lay hp hz hcG hcQ)
    (jointMulWindow_relCT hL hInit hm hC ha hD hOne hOneVal hG hQ hc hf ht hcache hseed hctr hu hv)

end VG.Proof.Weierstrass.X86_64
