module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Verified
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA's key search on AArch64 returns without secret residue

`vg_rsa_key_search` as emitted (`Impl.RsaKeyGen.AArch64.Fn.keySearch`), for
every implementation of the Miller–Rabin round. What the cleanup needs of the
code is evaluated once for the controller and once for the search, each with
nothing in the place of the function it calls; the candidate's follows from
its implementation's (`RoundImpl.side`, `RoundImpl.mmSide`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG VG.AArch64 VG.AArch64.Scrub VG.Proof.MillerRabin.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate

/-- No instruction of `vg_rsa_keygen_candidate` writes PSTATE.DIT, and it
calls nothing indirectly. -/
theorem candidate_side (v : RoundImpl) :
    sideAll (fun i => !i.writesDit)
      (Impl.RsaKeyGen.AArch64.Fn.candidate v.suffix v.mont.mm v.roundMont.mm) = true := by
  simp only [Impl.RsaKeyGen.AArch64.Fn.candidate, codeWith, kMainWith, millerRabinWith, mrRoundWith, montSetup,
    mrWitness, mrResult, loadC, closeCheck, trial, gcdCheck, gcdE, loadE, modLoop, finNone, finUsed, finPrime,
    subA, trialEntry, Impl.Rsa.AArch64.Keys.loadA, Impl.RsaKeyGen.AArch64.Candidate.halfPass,
    Impl.RsaKeyGen.AArch64.Candidate.expSetup, Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld,
    Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice,
    Impl.RsaKeyGen.AArch64.Candidate.lowWord, Impl.RsaKeyGen.AArch64.Candidate.halfCond,
    Impl.MillerRabin.AArch64.Caller.call, List.cons_append, List.nil_append, ite_true,
    Impl.Bignum.AArch64.seqs, sideAll, Bool.and_eq_true, v.mmSide, v.side, true_and]
  and_intros
  all_goals kernel_rfl

/-- The search with nothing in the place of the candidate. -/
theorem search_side_closed : sideAll (fun i => !i.writesDit)
    (Impl.RsaKeyGen.AArch64.Search.code (.call "" (.block []))) = true := by lit_decide

/-- The controller with nothing in the place of the search. -/
theorem controller_side_closed : sideAll (fun i => !i.writesDit)
    (Impl.RsaKeyGen.AArch64.Generate.code (.call "" (.block [])) keyCall) = true := by lit_decide

/-- `vg_rsa_key_search`. -/
theorem keySearch_scrubbed [Key.KeyProof] (v : RoundImpl) :
    VerifiedScrubbed target (Impl.RsaKeyGen.AArch64.Fn.keySearch v.suffix v.mont.mm v.roundMont.mm)
      (Spec.RsaKeyGen.keySearchContract abi stackUse) 32 := by
  obtain ⟨hs, -⟩ := side_depth_of_fill2 (d := 13)
    (c := Impl.RsaKeyGen.AArch64.Fn.primeSearch v.suffix v.mont.mm v.roundMont.mm)
    (a := .call ("vg_rsa_keygen_candidate" ++ v.suffix)
      (Impl.RsaKeyGen.AArch64.Fn.candidate v.suffix v.mont.mm v.roundMont.mm))
    (b := .block []) (e := Impl.RsaKeyGen.AArch64.Search.code (.call "" (.block []))) (da := 0) (db := 0)
    (by kernel_rfl) (candidate_side v) (Nat.le_of_eq (Search.depth_of_noFrames (Search.candidate_noFrames v)))
    (by rfl) (Nat.le_refl _) search_side_closed (Nat.le_of_ble_eq_true (by kernel_rfl))
  obtain ⟨hs', hd'⟩ := side_depth_of_fill2 (d := 26)
    (c := Impl.RsaKeyGen.AArch64.Generate.code
      (.call ("vg_rsa_prime_search" ++ v.suffix)
        (Impl.RsaKeyGen.AArch64.Fn.primeSearch v.suffix v.mont.mm v.roundMont.mm)) keyCall)
    (a := .call ("vg_rsa_prime_search" ++ v.suffix)
      (Impl.RsaKeyGen.AArch64.Fn.primeSearch v.suffix v.mont.mm v.roundMont.mm))
    (b := .block []) (e := Impl.RsaKeyGen.AArch64.Generate.code (.call "" (.block [])) keyCall)
    (da := 13) (db := 0)
    (by kernel_rfl) hs (Nat.le_of_eq (searchCode_depth v)) (by rfl) (Nat.le_refl _) controller_side_closed
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 416) (gen_verified v) (Proof.Rsa.AArch64.Scrub.keySearchOk stackUse) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd') (by decide)) hs' (.inr (.inl rfl))

end VG.Proof.RsaKeyGen.AArch64.Generate
