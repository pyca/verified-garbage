import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.Jac

/-!
# Doubling a Jacobian point in place, on x86-64

`dblJMul S p p` reads each coordinate of `p` before it overwrites it, so on
distinct slots (`dblInSlots`) it computes `dblJF` of `p`'s coordinates
(`dblIn_run`); `doubleIn` is then a doubling the Jacobian window method can
use, for any curve with `a = -3` and any number of words (`doubleIn_dblOk`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- The slots of the in-place doubling. -/
def dblInSlots (S : RcbSlots) (p : Pt) : List Nat := [S.t0, S.t1, S.t2, S.t3, p.x, p.y, p.z]

theorem dblIn_run {F : Type _} [Lean.Grind.CommRing F] (S : RcbSlots) (p : Pt) (E : Nat → F)
    (hd : (dblInSlots S p).Nodup) :
    (runOps (dblJMul S p p) E p.x, runOps (dblJMul S p p) E p.y, runOps (dblJMul S p p) E p.z) =
      dblJF (E p.x) (E p.y) (E p.z) := by
  simp only [dblInSlots, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨⟨h01, h02, h03, h04, h05, h06⟩, ⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩,
    ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, _⟩
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h65 := Ne.symm h56
  simp only [dblJMul, runOps, List.foldl, FOp.run, Function.update_apply, dblJF, Prod.mk.injEq, *,
    ite_true, ite_false]
  constructor
  · grind
  constructor <;> grind

theorem dblIn_reads (S : RcbSlots) (p : Pt) : readsOk (dblJMul S p p) [p.x, p.y, p.z] = true := by
  simp [dblJMul, readsOk, FOp.ins, FOp.out]

theorem dblIn_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop} (h : ∀ x ∈ dblInSlots S p, Sl x) :
    ∀ op ∈ dblJMul S p p, ∀ x ∈ op.out :: op.ins, Sl x := by
  intro op hop x hx
  apply h x
  simp only [dblJMul, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    simp only [dblInSlots, List.mem_cons, List.not_mem_nil, or_false] <;> grind

theorem dblIn_sub (S : RcbSlots) (p : Pt) : dblInSlots S p ⊆ rcbW S p := by
  intro x hx
  simp only [dblInSlots, rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  grind

/-- The in-place doubling doubles a Jacobian triple, for a curve with `a = -3`. -/
theorem doubleIn_dblOk {M : Mod} {C : Curve} (hm : UnitMod C.p (2 ^ (64 * M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} : DblOk M S C (doubleIn M S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  have hd : (dblInSlots S p).Nodup := by
    simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    simp only [dblInSlots, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    grind
  have hS : ∀ x ∈ dblInSlots S p, Sl x := fun x hx => hSl x (dblIn_sub S p hx)
  refine WP.mono (ForwardField.programB_ok hL hm _ hI (dblIn_slots hS) (dblIn_reads S p)) fun t ⟨k, I⟩ =>
    ⟨k.mono fun x hx => ?_, _, I.sub fun x hx => ?_,
      InvJ.dbl' hC ha hQ hJ (dblIn_run S p E hd)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    exact dblIn_sub S p (dblIn_slots (fun _ h => h) op hop op.out (List.mem_cons_self ..))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [dblJMul, validAfter, FOp.out]

/-- `doubleIn_dblOk` with the products written out (`Mod.inl`). -/
theorem doubleIn_dblOk_inl {M : Mod} {C : Curve} (hm : UnitMod C.p (2 ^ (64 * M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} (b : Bool) : DblOk M S C (doubleIn { M with inl := b } S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  exact WP.mono (doubleIn_dblOk (M := { M with inl := b }) hm hC ha (hL.inl b) hnd hSl (hI.inl b) hQ hJ)
    fun t ⟨k, E', I, J⟩ => ⟨k.of_inl, E', I.of_inl, J⟩

end VG.Proof.Weierstrass.X86_64
