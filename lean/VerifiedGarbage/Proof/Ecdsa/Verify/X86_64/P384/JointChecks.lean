module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P384.X86_64.JointLayout
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P384.X86_64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P384.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P384.X86_64.Joint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Proof.P384.X86_64.JacTiming
public import VerifiedGarbage.Proof.Framework.TaintMap
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.P384.X86_64.JacTiming
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Proof.P384.X86_64.JointPartsLit
import VerifiedGarbage.Proof.P384.X86_64.JointPartsLitAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Proof.P384.X86_64.JointPartsLit
meta import VerifiedGarbage.Proof.P384.X86_64.JointPartsLitAdx
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.Jac
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Weierstrass.Env
meta import VerifiedGarbage.Proof.Weierstrass.Law3
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! ### `Weierstrass.X86_64.JointDoubleIn`, which only this module used -/

section

/-!
# The joint loop's doublers in place

The accumulator doubled in place, with no copy from a temporary point:
`doubleIn` (`doubleIn_doubler`, any number of words) and, for P-384's `p`
with BMI2 and ADX, `doubleCms` with its small multiples fused
(`doubleCms_doubler`). Both are field programs over every slot the loop keeps
live, so the loop's other values survive them as they are.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

theorem stepsReadOk_mono : ∀ {l : List DStep} {V V' : List Nat}, stepsReadOk l V = true →
    (∀ x ∈ V, x ∈ V') → stepsReadOk l V' = true
  | [], _, _, _, _ => rfl
  | st :: l, V, V', h, hV => by
    simp only [stepsReadOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨fun x hx => hV x (h.1 x hx), stepsReadOk_mono h.2 fun x hx => ?_⟩
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hV x hx)

/-- `doubleIn` of the accumulator is a doubler of the joint loop. -/
theorem doubleIn_doubler {c : Joint.Cfg} {C : Curve} {size : Nat}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hnd : (rcbW c.K.S c.K.R).Nodup) (hct : ScratchCT (doubleIn c.K.M c.K.S c.K.R).inline) :
    JointDoubler c C size (doubleIn c.K.M c.K.S c.K.R) := by
  have hd : (dblInSlots c.K.S c.K.R).Nodup := by
    simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    simp only [dblInSlots, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    grind
  have sl : ∀ x∈dblInSlots c.K.S c.K.R,x∈jointSlots c := by
    intro x hx; have := dblIn_sub c.K.S c.K.R hx; jslots
  have wk : ∀ x∈dblInSlots c.K.S c.K.R,x∈jointWork c := by
    intro x hx; have := dblIn_sub c.K.S c.K.R hx; jslots
  have hr : readsOk (dblJMul c.K.S c.K.R c.K.R) (jointLive c) = true :=
    readsOk_mono (dblIn_reads c.K.S c.K.R) (jointLive_R c)
  have outs : ∀ x∈(dblJMul c.K.S c.K.R c.K.R).map FOp.out,x∈dblInSlots c.K.S c.K.R := by
    intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    exact dblIn_slots (fun _ h => h) op hop op.out (List.mem_cons_self ..)
  constructor
  · intro base u v Q A External s hExt hA h
    refine WP.mono_syms (ForwardField.programB_ok hL.lookup.layout.lay hm _ h.field (dblIn_slots sl) hr)
      fun t ⟨k,I⟩ st => ?_
    have kw := k.mono fun x hx => wk x (outs x hx)
    exact ⟨kw,h.next hL.lookup.layout kw (I.sub fun x hx => (mem_validAfter _ _).mpr (Or.inl hx))
      (InvJ.dbl' hC ha hA h.point (dblIn_run c.K.S c.K.R _ hd)) (hExt s t kw st h.external)⟩
  · intro base E
    exact (fieldProgram_relCT hct fun _ hi => WP.mono (ForwardField.programB_ok hL.lookup.layout.lay hm _ hi
      (dblIn_slots sl) hr) fun _ ht => ht.2).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)⟩)

/-- `doubleCms` of the accumulator is a doubler of the joint loop, for a
modulus `cms` reduces (`Mod.sparse`). -/
theorem doubleCms_doubler {c : Joint.Cfg} {C : Curve} {size : Nat}
    (hL : JointAddLayout c size) (hsp : c.K.M.sparse = true) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hnd : (rcbW c.K.S c.K.R).Nodup)
    (hct : ScratchCT (doubleCms c.K.M c.K.S c.K.R).inline) :
    JointDoubler c C size (doubleCms c.K.M c.K.S c.K.R) := by
  have sl : ∀ x∈rcbW c.K.S c.K.R,x∈jointSlots c := by intro x hx; jslots
  have wk : ∀ x∈rcbW c.K.S c.K.R,x∈jointWork c := by intro x hx; jslots
  have small : ∀ st∈dblCmsSteps c.K.S c.K.R,st.small = true := by
    intro st hst
    simp only [dblCmsSteps, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> rfl
  have hr : stepsReadOk (dblCmsSteps c.K.S c.K.R) (jointLive c) = true :=
    stepsReadOk_mono (dblCms_reads c.K.S c.K.R) (jointLive_R c)
  have run : ∀ {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State},
      Inv c.K.M base size C.p (·∈jointSlots c) V E s → stepsReadOk (dblCmsSteps c.K.S c.K.R) V = true →
      WP isa (doubleCms c.K.M c.K.S c.K.R).inline s fun t =>
        ProgKeep c.K.M base ((dblCmsSteps c.K.S c.K.R).map DStep.out) s t ∧
        Inv c.K.M base size C.p (·∈jointSlots c) (stepsValid (dblCmsSteps c.K.S c.K.R) V)
          (runSteps (dblCmsSteps c.K.S c.K.R) E) t := fun hI hR =>
    (blocks_wp _).mpr (dsteps_ok hsp hL.lookup.layout.lay hm _ hI small (dblCms_slots sl) hR)
  have outs : ∀ x∈(dblCmsSteps c.K.S c.K.R).map DStep.out,x∈rcbW c.K.S c.K.R := by
    intro x hx
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
    exact dblCms_slots (fun _ h => h) st hst st.out (List.mem_cons_self ..)
  constructor
  · intro base u v Q A External s hExt hA h
    refine WP.mono_syms (run h.field hr) fun t ⟨k,I⟩ st => ?_
    have kw := k.mono fun x hx => wk x (outs x hx)
    exact ⟨kw,h.next hL.lookup.layout kw (I.sub fun x hx => mem_stepsValid _ _ (Or.inl hx))
      (InvJ.dbl' hC ha hA h.point (dblCms_run c.K.S c.K.R _ hnd)) (hExt s t kw st h.external)⟩
  · intro base E
    exact (fieldProgram_relCT hct fun _ hi => WP.mono (run hi hr) fun _ ht => ht.2).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub fun x hx => mem_stepsValid _ _ (Or.inl hx)⟩)

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `P384.X86_64.JointTiming`, which only this module used -/

section

/-! Baseline and ADX taint checks of the rest of P-384's joint loop: its digits'
reads and entries, the cache of `Z²`, `Z³`, the seed, the counter, the
recoders and the doubler. -/

@[expose] public section

namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,?_,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_cached_checks : JointCachedChecks publicJointAdx := by
  refine ⟨?_,?_,nafCachedJac_adx_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_fixed_checks : JointFixedChecks publicJoint := by
  refine ⟨?_,?_,nafMixedJac_checks,joint_cached_checks.copy⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taintSym ["VG_P384_GTAB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_fixed_checks : JointFixedChecks publicJointAdx := by
  refine ⟨?_,?_,nafMixedJac_adx_checks,joint_adx_cached_checks.copy⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taintSym ["VG_P384_GTAB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct : ScratchCT (Joint.cacheCode publicJoint).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_adx_ct :
    ScratchCT (Joint.cacheCode publicJointAdx).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJointAdx.K publicJointAdx.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJoint)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJointAdx)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_checks : FastPrepChecks 6 (p384v.sl V) p384v.winBits 5 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 6))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator16_checks : FastPrepChecks16 6 (p384v.sl U) 6400 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 6))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_adx_checks : FastPrepChecks 6 (p384vx.sl V) p384vx.winBits 5 := fastPeer_checks

theorem fastGenerator16_adx_checks : FastPrepChecks16 6 (p384vx.sl U) 6400 := fastGenerator16_checks

theorem jointDouble_ct : ScratchCT (jointDouble publicJoint.K).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem jointDouble_adx_ct : ScratchCT (jointDoubleAdx publicJointAdx.K).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P384.X86_64

end

end

/-! ### `P384.X86_64.NafTableTiming`, which only this module used -/

section

/-! Baseline and ADX taint checks for P-384's verifier's odd-multiple table.

The field arithmetic is checked without its displacements, as the
templates of its operations (`FieldTmpl`), each analysed once; so is the
addition that keeps `rbx` (`KeepReg.keepsN`, which the kernel evaluates
once for each template from the same state). -/

@[expose] public section

namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTableCoZ_checks : NafTableCoZChecks nafJacWin := by
  have hT : p384T.Ok nafJacWin.M := p384HT_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafTableCoZ_adx_checks : NafTableCoZChecks nafJacWinAdx := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XHT_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P384.X86_64

end

end

/-! Concrete timing checks and the doubler of P-384's baseline and ADX joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P384.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p384v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTableCoZ_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator16_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p384vx publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTableCoZ_adx_checks,nafCacheTable_adx_ct,
    joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator16_adx_checks,fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p384v) (hC : Weierstrass.Law p384v.C) :
    JointDoubler publicJoint p384v.C size (jointDouble publicJoint.K) :=
  doubleIn_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    (by decide) jointDouble_ct

theorem joint_adx_doubler (hc : CfgOk p384vx) (hC : Weierstrass.Law p384vx.C) :
    JointDoubler publicJointAdx p384vx.C size (jointDoubleAdx publicJointAdx.K) :=
  doubleCms_doubler joint_adx_add_layout (by decide +kernel) (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    (by decide) jointDouble_adx_ct

/-- `jointPrefix p384v` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p384v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p384v).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `jointPrefix p384vx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixAdxErased : Prog isa := Code.erase (jointPrefix p384vx)

materialize_shared jointPrefixAdxErased

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384vx) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixAdxErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p384vx).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailAdxErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384vx).inline

materialize_shared jointTailAdxErased

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384vx).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailAdxErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P384
