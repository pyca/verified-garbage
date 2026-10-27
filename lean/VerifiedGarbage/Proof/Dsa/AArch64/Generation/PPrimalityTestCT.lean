module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestFullCT

/-! # Public width rejection and full-width primality form one native p test -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def PPrimalityTestBefore (len : Nat) (p : PPrimalityPublic) (s : State) : Prop :=
  PPrimalityAfter p s ∧ p.plan.construct.len = len

theorem pPrimalityTest_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PPrimalityTestBefore len)) (pTest T.run len) (fun _ _ => True) := by
  intro s t a b s' t' h es et
  obtain ⟨p, ⟨hs, he⟩, ⟨ht, _⟩, hsp⟩ := h
  by_cases small : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len - 1)
  · exact pTest_small_ct T.run len s t a b s' t'
      ⟨p.width hs.fits, ⟨pPrimality_width hs, small⟩, ⟨pPrimality_width ht, small⟩, hsp⟩ es et
  · let domain : VG.Proof.Dsa.Generation.PDomain p.plan.construct.len p.plan.construct.value :=
      ⟨p.plan.construct.width, hs.odd, Nat.le_of_not_gt small, hs.fits⟩
    subst he
    let full : PTestFullPublic p.plan.construct.len := ⟨p.width hs.fits, p.primeCall domain, small⟩
    have state : ∀ u, PPrimalityAfter p u → PTestFullBefore p.plan.construct.len full u :=
      fun u hu => ⟨pPrimality_primeCall hu domain, pPrimality_width hu⟩
    exact pTest_full_ct T _ hlen s t a b s' t' ⟨full, state s hs, state t ht, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation
