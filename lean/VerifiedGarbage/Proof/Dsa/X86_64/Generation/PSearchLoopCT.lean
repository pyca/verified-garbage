module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq

/-! # Timing of the bounded native p search, including its exact retry cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private def searchLoopInv (n pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchBefore n pLen qLen p s

section
variable (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
variable (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
variable (sizes : GenerationSizes pLen qLen)
variable (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
variable (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
variable (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
variable (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
variable (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
variable (hd : (if qLen = 20 then G1 else G256).D = qLen)

include hG hmatch hsize hhash hseedsize hd sizes

theorem searchIteration_ready {p : SearchPublic} {s : State} (h : SearchBefore n pLen qLen p s) :
    WP isa (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) s (SearchIterationAfter n pLen qLen p) := by
  unfold pSearchIteration
  simp only [seqs]
  refine WP.seq (WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
    fun _ ht => searchIteration_tail ⟨ht, h.2.2.2.2.2⟩ ?_ ?_)
  all_goals rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

include hn

private theorem searchLoop_step (remaining : Nat) :
    RelCT isa (searchLoopInv n pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (fun s t => isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ next < remaining, searchLoopInv n pLen qLen next s t)) := by
  have step : RelCT isa (searchLoopInv n pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchIterationAfter n pLen qLen p s) := by
    refine two_post ((searchIteration_ct G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (searchIteration_ready G1 G256 T n H pLen qLen sizes hG hmatch hsize hhash hseedsize hd h.2)
      fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have next := hs.2 cont
  have bound : p.counter + 1 < 32 * pLen := by
    have hb := (of_decide_eq_true cont).2
    rw [show p.plan.attempt.construct.len = pLen from next.2.2.2.2.2.1] at hb
    exact hb
  refine ⟨32 * pLen - (p.counter + 1), by omega, p.next cont, ⟨rfl, next⟩, rfl, ht.2 cont⟩

theorem pSearchLoop_ct : RelCT isa (Two (SearchBefore n pLen qLen))
    (.loop (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) .e) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht⟩ es et
  exact RelCT.loop (searchLoopInv n pLen qLen)
    (searchLoop_step G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd)
    (32 * pLen - p.counter) s t a b s' t' ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ es et

end
end VG.Proof.Dsa.X86_64.Generation
