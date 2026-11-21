module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Instances
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Verified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Ffdh.AArch64.Fn
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill

/-!
# FFDH on AArch64: its functions return without secret residue

Each function as emitted (`Impl.Ffdh.AArch64.Fn`), cleanup included: it meets
its contract in constant time and returns without secret residue. What the
cleanup needs of the code is evaluated here, by the kernel; the search of the
parameters', for every implementation of the Miller–Rabin round, with nothing
in the place of the candidate, whose own follows from its implementation's
(`RoundImpl.side`, `RoundImpl.mmSide`).
-/

-- separate module: the kernel's evaluation of the scrub's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Scrub

open VG VG.AArch64 VG.AArch64.Scrub

/-- `vg_ffdh_generate_key_precompute`. -/
theorem precompute_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.precompute
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts Impl.Ffdh.AArch64.Cached.Policy.tableConsts) 0) 32 :=
  verifiedScrubbedOf0 (Proof.Ffdh.AArch64.Cached.precompute_verified Proof.Bignum.AArch64.Mont.productEight)
    (generationPrecomputeOk _ _ _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_generate_key_search_cached`. -/
theorem cachedKeySearch_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.cachedKeySearch (Spec.Ffdh.cachedKeySearchContract abi 64) 32 :=
  verifiedScrubbedOf (W := 64) Proof.Ffdh.AArch64.Cached.cachedSearch_verified (cachedKeySearchOk _)
    (by decide) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_check_public`. -/
theorem checkPublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.checkPublic (Spec.Ffdh.checkPublicContract abi 0) 32 :=
  verifiedScrubbedOf0 (Proof.Ffdh.AArch64.CheckPublic.cp_verified
      Proof.Bignum.AArch64.WindowFive.called Proof.Bignum.AArch64.Mont.base
      Proof.Bignum.AArch64.WindowVector.selector)
    (checkPublicOk _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_check_domain`. -/
theorem checkDomain_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.checkDomain
      (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.AArch64.Cached.Policy.tableConsts) 0) 32 :=
  verifiedScrubbedOf0
    (Proof.Ffdh.AArch64.VettedValidation.verified
      Proof.Bignum.AArch64.WindowFive.called Proof.Bignum.AArch64.Mont.base
      Proof.Bignum.AArch64.WindowVector.selector)
    (checkDomainOk _ _ _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_exchange`. -/
theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.exchange (Spec.Ffdh.exchangeContract abi 0) 32 :=
  verifiedScrubbedOf0 (Proof.Ffdh.AArch64.Exchange.ex_verified
      Proof.Bignum.AArch64.WindowFive.called Proof.Bignum.AArch64.Mont.base
      Proof.Bignum.AArch64.WindowVector.selector)
    (exchangeOk _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_check_private`. -/
theorem checkPrivate_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.checkPrivate (Spec.Ffdh.checkPrivateContract abi 0) 32 :=
  verifiedScrubbedOf0 (Proof.Ffdh.AArch64.CheckPrivate.kp_verified
      Proof.Bignum.AArch64.WindowFive.called Proof.Bignum.AArch64.Mont.base
      Proof.Bignum.AArch64.WindowVector.selector)
    (checkPrivateOk _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_derive_public`. -/
theorem derivePublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Fn.derivePublic (Spec.Ffdh.derivePublicContract abi 0) 32 :=
  verifiedScrubbedOf0 (Proof.Ffdh.AArch64.Derive.dv_verified
      Proof.Bignum.AArch64.WindowFive.called Proof.Bignum.AArch64.Mont.base
      Proof.Bignum.AArch64.WindowVector.selector)
    (derivePublicOk _) (by lit_decide) (by lit_decide) (.inr (.inl rfl))

/-- `vg_ffdh_parameter_init`, whose code leaves nothing to clear. -/
theorem parameterInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.Generation.init (Spec.Ffdh.parameterInitContract abi) 32 :=
  ⟨Proof.Ffdh.AArch64.Generation.init_verified, Proof.Ffdh.AArch64.Generation.init_noResidue _ _⟩

/-- `vg_ffdh_key_init`, whose code leaves nothing to clear. -/
theorem keyInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.AArch64.KeyGeneration.init (Spec.Ffdh.keyInitContract abi) 32 :=
  ⟨Proof.Ffdh.AArch64.KeyGeneration.init_verified, Proof.Ffdh.AArch64.KeyGeneration.init_noResidue _ _⟩

end VG.Proof.Ffdh.AArch64.Scrub

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.AArch64.Scrub
open VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MillerRabin.AArch64 (RoundImpl)

/-- No instruction of `vg_ffdh_parameter_candidate_sieved` writes PSTATE.DIT,
and it calls nothing indirectly. -/
theorem parameterCandidate_side (v : RoundImpl) :
    sideAll (fun i => !i.writesDit)
      (Impl.Ffdh.AArch64.Fn.parameterCandidate v.suffix v.mont.mm v.roundMont.mm) = true := by
  simp only [Impl.Ffdh.AArch64.Fn.parameterCandidate, code, main, mainQ, mainP, tests, testQ, testRest, test,
    firstCheck, restChecks, phase, shapeP, residue, sieve, halveQ, montPrep, millerRabin, draw, round, pResult,
    qResult, Impl.Rsa.AArch64.Keys.loadA, Impl.RsaKeyGen.AArch64.Candidate.trialEntry,
    Impl.RsaKeyGen.AArch64.Candidate.halfPass, Impl.RsaKeyGen.AArch64.Candidate.subA,
    Impl.RsaKeyGen.AArch64.Candidate.expSetup, Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld,
    Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice,
    Impl.RsaKeyGen.AArch64.Candidate.lowWord, Impl.RsaKeyGen.AArch64.Candidate.halfCond,
    Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false, Bool.false_eq_true,
    Impl.Bignum.AArch64.seqs, sideAll, Bool.and_eq_true, v.mmSide, v.side, true_and]
  and_intros
  all_goals kernel_rfl

/-- The search with nothing in the place of the candidate. -/
theorem search_side_closed : sideAll (fun i => !i.writesDit)
    (Impl.Ffdh.AArch64.Generation.Search.code (.call "" (.block []))) = true := by lit_decide

/-- `vg_ffdh_generate_parameters`'s search, with each implementation of the
Miller–Rabin round. -/
theorem parameterSearch_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Ffdh.AArch64.Fn.parameterSearch v.suffix v.mont.mm v.roundMont.mm)
      (Spec.Ffdh.sievedParameterSearchContract abi stackUse) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2 (d := 2)
    (c := Impl.Ffdh.AArch64.Generation.Search.code
      (.call ("vg_ffdh_parameter_candidate_sieved" ++ v.suffix)
        (Impl.Ffdh.AArch64.Fn.parameterCandidate v.suffix v.mont.mm v.roundMont.mm)))
    (a := .call ("vg_ffdh_parameter_candidate_sieved" ++ v.suffix)
      (Impl.Ffdh.AArch64.Fn.parameterCandidate v.suffix v.mont.mm v.roundMont.mm))
    (b := .block []) (e := Impl.Ffdh.AArch64.Generation.Search.code (.call "" (.block []))) (da := 0) (db := 0)
    (by kernel_rfl) (parameterCandidate_side v) (Nat.le_of_eq (depth_of_noFrames (candidate_noFrames v)))
    (by rfl) (Nat.le_refl _) search_side_closed (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 32) (search_verified v) (Scrub.sievedParameterSearchOk _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

end VG.Proof.Ffdh.AArch64.Generation
