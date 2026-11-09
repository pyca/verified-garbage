module

public import VerifiedGarbage.Proof.P256.X86_64.DoubleHalf
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState

/-! Memory and point invariant for the in-place P-256 doubling schedule. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Spec.Weierstrass

theorem doubleHalf_before_reads (S : RcbSlots) (p : Pt) :
    readsOk (DoubleHalf.before S p) [p.x,p.y,p.z]=true := by
  simp [DoubleHalf.before,readsOk,FOp.ins,FOp.out]

theorem doubleHalf_after_reads (S : RcbSlots) (p : Pt) (V : List Nat) :
    readsOk (DoubleHalf.after S p) (S.t1 :: validAfter (DoubleHalf.before S p) V)=true := by
  simp [DoubleHalf.before,DoubleHalf.after,readsOk,validAfter,FOp.ins,FOp.out]

theorem doubleHalf_before_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop}
    (h : ∀ x∈doubleSlots S p,Sl x) :
    ∀ op∈DoubleHalf.before S p,∀ x∈op.out::op.ins,Sl x := by
  intro op hop x hx
  apply h x
  simp only [DoubleHalf.before,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
    simp only [doubleSlots,List.mem_cons,List.not_mem_nil,or_false] <;> grind

theorem doubleHalf_after_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop}
    (h : ∀ x∈doubleSlots S p,Sl x) :
    ∀ op∈DoubleHalf.after S p,∀ x∈op.out::op.ins,Sl x := by
  intro op hop x hx
  apply h x
  simp only [DoubleHalf.after,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
    simp only [doubleSlots,List.mem_cons,List.not_mem_nil,or_false] <;> grind

end VG.Proof.P256.X86_64
