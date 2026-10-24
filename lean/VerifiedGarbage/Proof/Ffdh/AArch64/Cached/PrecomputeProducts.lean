module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeProduct
import VerifiedGarbage.Proof.Framework.Omega

/-! Fill all subsets containing the current tooth on a fixed public loop schedule. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

theorem precomputeProducts_ok (M : Mont) {s : State} {p : Parameters} {b : Nat}
 (h : ProductState p b 1 s) (positive : 0<b) :
 WP isa (.loop (Precompute.product M.mm) (.nonzero .x .x3)) s fun t =>
 ProductState p b (2^b) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by have := h.tooth;omega : b≤4)
 have atLeast : (2:Nat)^1≤2^b := Nat.pow_le_pow_right (by decide) (by omega : 1≤b)
 let I := fun i t => ProductState p b (i+1) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t
 have step (i : Nat) (hi : i<2^b-1) (t : State) (inv : I i t) :
  WP isa (Precompute.product M.mm) t fun u => I (i+1) u ∧ ((u.gpr .x3).toNat≠0 ↔ i+1≠2^b-1) := by
  refine WP.mono (precomputeProduct_ok M inv.1 (by omega)) ?_
  rintro u ⟨state,index,frame,rest⟩
  refine ⟨⟨state,inv.2.1.trans frame,(inv.2.2.trans rest).mono (by simp [mmRegs])⟩,?_⟩
  rw [index,BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
   Nat.mod_eq_of_lt (by omega : i+1+1<2^64),Nat.mod_eq_of_lt (by omega : 2^b<2^64)]
  omega
 refine WP.mono (count_loop (by omega : 0<2^b-1) I step
  ⟨h,Frame.refl _ _,Keep.refl _ _⟩) ?_
 rintro t ⟨state,frame,rest⟩
 have final : 2^b-1+1=2^b := by omega
 rw [final] at state
 exact ⟨state,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
