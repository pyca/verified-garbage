module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidthCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
/-! # Public width rejection and full-width primality form one native p test -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PTestFullCT.lean`, which only this module imported.
section

/-! # Full-width candidates proceed to the probable-prime call -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure PTestFullPublic (len : Nat) where
  width : CandidateWidthPublic
  call : PrimeTestPublic (8 * len)
  full : ¬ width.value < 2 ^ (8 * width.len - 1)

def PTestFullBefore (len : Nat) (p : PTestFullPublic len) (s : State) : Prop :=
  PrimeTestBefore (8 * len) p.call s ∧ CandidateWidthBefore p.width s

theorem pTestFull_ready {len : Nat} {p : PTestFullPublic len} {s : State}
    (h : PTestFullBefore len p s) : WP isa (.block candidateWidth) s fun t =>
      PrimeTestBefore (8 * len) p.call t ∧ eval (.zero .x .x3) t = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  obtain ⟨W, V, hi⟩ := h.1
  exact ⟨⟨W, V, hi.congr hm hk.sp hk.rd hk.wr⟩, by simpa only [decide_eq_false p.full] using cf⟩

theorem pTest_full_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest T.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _, _⟩
    cases Option.some.inj (hs.1.2.symm.trans hs.2)
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct T
    rcases hlen with rfl | rfl | rfl <;> unfold ProbablePrime.Supported <;> decide

end VG.Proof.Dsa.AArch64.Generation
end

end

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
