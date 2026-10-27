module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Full-width candidates proceed to the probable-prime call -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure PTestFullPublic (len : Nat) where
  width : CandidateWidthPublic
  call : PrimeTestPublic (8 * len)
  full : ¬ width.value < 2 ^ (8 * width.len - 1)

def PTestFullBefore (len : Nat) (p : PTestFullPublic len) (s : State) : Prop :=
  PrimeTestBefore (8 * len) p.call s ∧ CandidateWidthBefore p.width s

theorem pTestFull_ready {len : Nat} {p : PTestFullPublic len} {s : State}
    (h : PTestFullBefore len p s) : WP isa (.block candidateWidth) s fun t =>
      PrimeTestBefore (8 * len) p.call t ∧ t.cf = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  obtain ⟨W, V, hi⟩ := h.1
  exact ⟨⟨W, V, hi.congr hm (hk.gpr (by decide)) hk.2.1 hk.2.2⟩, by simp [cf, p.full]⟩

theorem pTest_full_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest T.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _⟩
    simpa only [eval, hs.1.2, Bool.false_eq_true, Option.some.injEq] using hs.2
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct T
    rcases hlen with rfl | rfl | rfl <;> unfold ProbablePrime.Supported <;> decide

end VG.Proof.Dsa.X86_64.Generation
