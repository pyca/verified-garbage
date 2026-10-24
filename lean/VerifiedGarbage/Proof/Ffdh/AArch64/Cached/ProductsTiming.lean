module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ProductTiming
import VerifiedGarbage.Proof.Framework.Omega

/-! The subset loop performs exactly 2^b−1 iterations for its public tooth b. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure ProductsPublic where
 p : Parameters
 b : Nat
 positive : 0<b
 limit : b<5

def ProductsReady (q : ProductsPublic) (i : Nat) (s : State) : Prop := ProductState q.p q.b (i+1) s

theorem precomputeProducts_ct (M : Mont) : RelCT isa (Two fun q s =>ProductsReady q 0 s)
 (.loop (Precompute.product M.mm) (.nonzero .x .x3)) (fun _ _ =>True) := by
 have hct : RelCT isa (Two fun (q : ProductsPublic × Nat) s =>q.2<2^q.1.b-1 ∧ ProductsReady q.1 q.2 s)
  (Precompute.product M.mm) (fun _ _ =>True) :=
  two_map (fun q =>(⟨q.1.p,q.1.b,q.2+1⟩ : ProductPublic))
   (fun q s h =>⟨by change q.2+1<2^q.1.b;omega,h.2⟩) (precomputeProduct_ct M)
 have loop := two_loop (cond:= .nonzero .x .x3) (Φ:=ProductsReady) (Ψ:=fun _ _ =>True) (fun q =>2^q.b-1) hct (by
  intro q i s hi h
  have bound : 2^q.b≤16 := Nat.pow_le_pow_right (by decide) (by have := q.limit;omega : q.b≤4)
  have atLeast : (2:Nat)^1≤2^q.b := Nat.pow_le_pow_right (by decide) (by have := q.positive;omega : 1≤q.b)
  refine WP.mono (precomputeProduct_ok M h (by omega : i+1<2^q.b)) ?_
  rintro t ⟨state,index,_,_⟩
  refine ⟨?_,fun _ =>state,fun _ =>trivial⟩
  rw [eval_nonzero,index,ne_zero_iff]
  have nonzero : ((BitVec.ofNat 64 (i+1+1)-BitVec.ofNat 64 (2^q.b)).toNat≠0) ↔ i+1<2^q.b-1 := by
   rw [BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i+1+1<2^64),Nat.mod_eq_of_lt (by omega : 2^q.b<2^64)]
   omega
  by_cases more : i+1<2^q.b-1
  · rw [decide_eq_true (nonzero.mpr more),decide_eq_true more]
  · have last : ¬(BitVec.ofNat 64 (i+1+1)-BitVec.ofNat 64 (2^q.b)).toNat≠0 := fun h =>more (nonzero.mp h)
    rw [decide_eq_false last,decide_eq_false more])
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>by
  have atLeast : (2:Nat)^1≤2^q.b := Nat.pow_le_pow_right (by decide) (by have := q.positive;omega : 1≤q.b)
  exact ⟨q,⟨by omega,hs⟩,⟨by omega,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
