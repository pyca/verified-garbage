module

public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalf
import VerifiedGarbage.Proof.P256.X86_64.HalfMemory
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.P256.X86_64.Half
public import VerifiedGarbage.Proof.Weierstrass.Jac

/-! ### `P256.X86_64.HalfField`, which only this module used -/

section

/-! The modular halving block acts as division by two on Montgomery field slots. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def halfFe (x : Fin Spec.P256.p) : Fin Spec.P256.p :=
  x * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)

private theorem two_inv :
    (2 : Fin Spec.P256.p) * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)=1 := by decide

private theorem mul_of_double {F : Type _} [Lean.Grind.CommRing F]
    {x y i : F} (hi : (2:F)*i=1) (h : y+y=x) : y=x*i := by
  have hy := congrArg (fun z => y*z) hi
  have hx := congrArg (fun z => z*i) h
  grind

theorem halfFe_of_double {x y : Fin Spec.P256.p} (h : y+y=x) : y=halfFe x := by
  exact mul_of_double two_inv h

theorem toM_halfValue (R : Nat) {x : Nat} (hx : x<Spec.P256.p) :
    toM Spec.P256.p R (halfValue x)=halfFe (toM Spec.P256.p R x) := by
  apply halfFe_of_double
  rw [←toM_add]
  have he : (halfValue x+halfValue x)%Spec.P256.p=x := by
    simpa only [Nat.two_mul] using halfValue_twice hx
  rw [he]

theorem half_inv_ok {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) {V : List Nat} {E : Nat → Fin Spec.P256.p}
    {s : State} (hI : Inv M base size Spec.P256.p Sl V E s) {o a : Nat}
    (ho : Sl o) (ha : a∈V) :
    WP isa (.block (half o a)) s fun t =>
      OpKeep M base o s t ∧
      Inv M base size Spec.P256.p Sl (o::V) (Function.update E o (halfFe (E a))) t := by
  have hao := hL.le a (hI.sl a ha)
  have hoo := hL.le o ho
  have hlt := hI.lt a ha
  rw [hn] at hao hoo hlt
  refine WP.mono (half_ok hI.scr hao hoo hlt) fun t ⟨he,ht,_,hk,hm⟩ => ?_
  have keep : OpKeep M base o s t := by
    refine ⟨fun r hr => hk.gpr r (fun h => hr ?_),hk.rd,hk.wr,?_⟩
    · rw [hn]
      apply List.mem_append_left
      change r∈[.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12,.r13]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with h|h|h|h|h|h|h|h|h <;> simp [h]
    · intro x hx _
      rw [hn] at hx
      exact hm x hx
  refine ⟨keep,hI.update hL ho keep ?_ ?_⟩
  · rw [hn]; exact ht
  · rw [hn,he,toM_halfValue _ hlt]
    have hv := hI.val a ha
    rw [hn] at hv
    rw [hv]

end VG.Proof.P256.X86_64

end

end


/-! The in-place halving schedule computes the usual Jacobian double. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.Impl.Weierstrass VG.Impl.P256.X86_64 VG.Proof.Weierstrass

def doubleSlots (S : RcbSlots) (p : Pt) : List Nat :=
  [S.t0,S.t1,S.t2,S.t3,S.t4,p.x,p.y,p.z]

def doubleHalfEnv (S : RcbSlots) (p : Pt) (E : Nat → Fin Spec.P256.p) : Nat → Fin Spec.P256.p :=
  let E₁ := runOps (DoubleHalf.before S p) E
  runOps (DoubleHalf.after S p) (Function.update E₁ S.t1 (halfFe (E₁ S.t1)))

private theorem half_fourth {F : Type _} [Lean.Grind.CommRing F]
    {y i : F} (hi : (2:F)*i=1) :
    ((y+y)*(y+y)*((y+y)*(y+y)))*i = 8*(y*y*(y*y)) := by
  have h := congrArg (fun z => (y*y*(y*y))*z) hi
  grind

theorem doubleHalfEnv_run (S : RcbSlots) (p : Pt) (E : Nat → Fin Spec.P256.p)
    (hd : (doubleSlots S p).Nodup) :
    (doubleHalfEnv S p E p.x,doubleHalfEnv S p E p.y,doubleHalfEnv S p E p.z)=
      dblJF (E p.x) (E p.y) (E p.z) := by
  have hi : (2 : Fin Spec.P256.p) * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)=1 := by decide
  have hh := half_fourth (y:=E p.y) hi
  simp only [doubleSlots,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hd
  rcases hd with ⟨⟨h01,h02,h03,h04,h05,h06,h07⟩,⟨h12,h13,h14,h15,h16,h17⟩,⟨h23,h24,h25,h26,h27⟩,⟨h34,h35,h36,h37⟩,⟨h45,h46,h47⟩,⟨h56,h57⟩,h67,_⟩
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
  simp only [doubleHalfEnv,DoubleHalf.before,DoubleHalf.after,runOps,List.foldl,FOp.run,
    Function.update_apply,halfFe,dblJF,Prod.mk.injEq, *,ite_true,ite_false]
  constructor
  · grind
  constructor <;> grind

end VG.Proof.P256.X86_64
