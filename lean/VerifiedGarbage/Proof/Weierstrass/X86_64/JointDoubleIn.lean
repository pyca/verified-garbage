module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.Jac
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
