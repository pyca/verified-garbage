module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqrVerified
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath

import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqr521Timing
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Framework.Contract

/-! The dedicated P-521 square meets the existing Montgomery square contract. -/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Impl.Weierstrass.Mont
open VG.Proof.Mont
open VG.Proof.Mont.AArch64.P521Square

theorem p521p_m : p521p.m = fieldPrime := by decide +kernel

theorem sqr521_a (s : State) (hs : (sqrA p521p).pre s) :
    ∃ t s', Exec isa sqrFn521 s t s' ∧ abiPreserved s s' ∧ (sqrA p521p).post s s' := by
  have hm := p521p_m
  obtain ⟨t, s', he, A, K, ⟨V, C⟩, -, -, -, -⟩ := square_fn_ok
    (pre_of (M := p521p) (by decide) hs.1)
    (by rw [← hm]; rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept (k := 9) (by decide) K⟩
  · rw [numAt_eq, hm]; exact V
  · simp only [argNum, numAt_eq, hm, Modulus.R]; exact C

theorem p521p_sqr_verified : Verified AArch64.target sqrFn521 (p521p.sqrContract AArch64.abi) :=
  Verified.of_correct sqr521_a p521p_sqr_ct
    { pre := by sig_implies_pre [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, sqr_sat p521p (by decide) (by decide +kernel)⟩ }

end VG.Proof.Weierstrass.AArch64.Mont
