module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# The joint loop's doublers in place

The accumulator doubled in place, with no copy from a temporary point:
`doubleIn` (`doubleIn_doubler`, any number of words) and, for P-384's `p`
with BMI2 and ADX, `doubleCms` with its small multiples fused
(`doubleCms_doubler`), for `a = -3`; and `doubleIn0` for `a = 0`
(`doubleIn0_doubler`). Both are field programs over every slot the loop keeps
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

/-- The slots of the in-place doubling for `a = 0`. -/
def dblIn0Slots (S : RcbSlots) (p : Pt) : List Nat := [S.t0, S.t1, S.t2, S.t3, S.t4, p.x, p.y, p.z]

theorem dblIn0_run {F : Type _} [Lean.Grind.CommRing F] (S : RcbSlots) (p : Pt) (E : Nat → F)
    (hd : (dblIn0Slots S p).Nodup) :
    (runOps (dblJ0 S p p) E p.x, runOps (dblJ0 S p p) E p.y, runOps (dblJ0 S p p) E p.z) =
      Weierstrass.dbl0F (E p.x) (E p.y) (E p.z) := by
  simp only [dblIn0Slots, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, _⟩
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h70 := Ne.symm h07
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h71 := Ne.symm h17
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h72 := Ne.symm h27
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h73 := Ne.symm h37
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h74 := Ne.symm h47
  have h65 := Ne.symm h56
  have h75 := Ne.symm h57
  have h76 := Ne.symm h67
  simp only [dblJ0, runOps, List.foldl, FOp.run, Function.update_apply, Weierstrass.dbl0F, *,
    ite_true, ite_false]

theorem dblIn0_reads (S : RcbSlots) (p : Pt) : readsOk (dblJ0 S p p) [p.x, p.y, p.z] = true := by
  simp [dblJ0, readsOk, FOp.ins, FOp.out]

theorem dblIn0_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop} (h : ∀ x ∈ dblIn0Slots S p, Sl x) :
    ∀ op ∈ dblJ0 S p p, ∀ x ∈ op.out :: op.ins, Sl x := by
  intro op hop x hx
  apply h x
  simp only [dblJ0, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    simp only [dblIn0Slots, List.mem_cons, List.not_mem_nil, or_false] <;> grind

theorem dblIn0_sub (S : RcbSlots) (p : Pt) : dblIn0Slots S p ⊆ rcbW S p := by
  intro x hx
  simp only [dblIn0Slots, rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  grind

/-- `doubleIn0` of the accumulator is a doubler of the joint loop, for a
curve with `a = 0`. -/
theorem doubleIn0_doubler {c : Joint.Cfg} {C : Curve} {size : Nat}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : Weierstrass.A0 C)
    (hnd : (rcbW c.K.S c.K.R).Nodup) (hct : ScratchCT (doubleIn0 c.K.M c.K.S c.K.R).inline) :
    JointDoubler c C size (doubleIn0 c.K.M c.K.S c.K.R) := by
  have hd : (dblIn0Slots c.K.S c.K.R).Nodup := by
    simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    simp only [dblIn0Slots, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    grind
  have sl : ∀ x∈dblIn0Slots c.K.S c.K.R,x∈jointSlots c := by
    intro x hx; have := dblIn0_sub c.K.S c.K.R hx; jslots
  have wk : ∀ x∈dblIn0Slots c.K.S c.K.R,x∈jointWork c := by
    intro x hx; have := dblIn0_sub c.K.S c.K.R hx; jslots
  have hr : readsOk (dblJ0 c.K.S c.K.R c.K.R) (jointLive c) = true :=
    readsOk_mono (dblIn0_reads c.K.S c.K.R) (jointLive_R c)
  have outs : ∀ x∈(dblJ0 c.K.S c.K.R c.K.R).map FOp.out,x∈dblIn0Slots c.K.S c.K.R := by
    intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    exact dblIn0_slots (fun _ h => h) op hop op.out (List.mem_cons_self ..)
  constructor
  · intro base u v Q A External s hExt hA h
    refine WP.mono_syms (ForwardField.programB_ok hL.lookup.layout.lay hm _ h.field (dblIn0_slots sl) hr)
      fun t ⟨k,I⟩ st => ?_
    have kw := k.mono fun x hx => wk x (outs x hx)
    have J := InvJ.dbl0 hC ha hA h.point
    rw [← dblIn0_run c.K.S c.K.R _ hd] at J
    exact ⟨kw,h.next hL.lookup.layout kw (I.sub fun x hx => (mem_validAfter _ _).mpr (Or.inl hx))
      J (hExt s t kw st h.external)⟩
  · intro base E
    exact (fieldProgram_relCT hct fun _ hi => WP.mono (ForwardField.programB_ok hL.lookup.layout.lay hm _ hi
      (dblIn0_slots sl) hr) fun _ ht => ht.2).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)⟩)

end VG.Proof.Weierstrass.X86_64
