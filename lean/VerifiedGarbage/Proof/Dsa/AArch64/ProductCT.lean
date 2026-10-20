module

public import VerifiedGarbage.Proof.Dsa.AArch64.Product
import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant time of DSA's ordinary modular product -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

/-- Public workspace data. The operands are deliberately absent. -/
structure ProductPublic where
  layout : Lay
  modulus : Nat
  fits : slot layout.w 8 ≤ layout.Z
  lower : 2 ≤ layout.w
  upper : layout.w < 2 ^ 31

/-- The modulus context and the arrays already known to be reduced. -/
def Reduced (arrays : List Nat) (p : ProductPublic) (s : State) : Prop :=
  ModCtx s p.layout.B p.layout.Z p.layout.w p.layout.minv p.modulus ∧
    ∀ j ∈ arrays, wv s.mem p.layout.B (slot p.layout.w j) p.layout.w < p.modulus

/-- A Montgomery step adds its result to the reduced arrays, preserving
all the others. Its operands can differ between runs. -/
theorem mont_step_ct (M : Mont) {o a b : Nat} (huse : MmUse o a b)
    (arrays : List Nat) (hb : b ∈ arrays)
    (valid : ∀ j ∈ arrays, j < 8 ∧ j ≠ aAcc ∧ j ≠ aTmp) :
    RelCT isa (Two (Reduced arrays)) (M.mm o a b) (Two (Reduced (o :: arrays))) := by
  refine two_post
    (two_map (fun p : ProductPublic => p.layout.ws)
      (fun p _ h => ⟨_, h.1.good, p.fits⟩) (M.ct huse)) ?_
  intro p s h
  obtain ⟨hc, hred⟩ := h
  refine WP.mono (mont_step M hc p.fits p.lower p.upper huse (hred b hb))
    fun t ⟨ht, hlt, _, hf, _⟩ => ⟨ht, ?_⟩
  intro j hj
  simp only [List.mem_cons] at hj
  rcases hj with rfl | hj
  · exact hlt
  by_cases heq : j = o
  · subst j
    exact hlt
  obtain ⟨hj8, hjacc, hjtmp⟩ := valid j hj
  have hnZ : p.layout.B.toNat + slot p.layout.w 8 ≤ 2 ^ 64 := by
    have := hc.good.scr.nowrap
    have := p.fits
    omega
  rw [hf.wv_of_not_mem hj8 (by simp [hjacc, hjtmp, heq]) hnZ]
  exact hred j hj

/-- The four calls in the ordinary product have traces independent of the
input values, including unreduced operands. R² and one are initially reduced. -/
theorem productCore_ct (M : Mont) :
    RelCT isa (Two (Reduced [aR2, aOne])) (Arithmetic.productCore M.mm) (fun _ _ => True) := by
  unfold Arithmetic.productCore seqs
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aX, aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aXm, aX, aR2, aOne] (by decide) (by decide))
  exact (mont_step_ct M (by unfold MmUse; decide) [aY, aXm, aX, aR2, aOne] (by decide) (by decide)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64
