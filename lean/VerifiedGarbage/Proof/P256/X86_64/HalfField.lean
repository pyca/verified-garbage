import VerifiedGarbage.Proof.P256.X86_64.HalfMemory
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-! The modular halving block acts as division by two on Montgomery field slots. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def halfFe (x : Fin Spec.P256.p) : Fin Spec.P256.p :=
  x * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)

private theorem two_inv :
    (2 : Fin Spec.P256.p) * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)=1 := by decide

theorem halfFe_double (x : Fin Spec.P256.p) : halfFe x + halfFe x=x := by
  have := two_inv
  unfold halfFe
  grind

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
