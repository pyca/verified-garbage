module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Correct
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Implies
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CTCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTFront
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTTail

/-! # The verified RSA prime search (AArch64)

For any candidate with no frames (`search_verified_of`), and for the
candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/AArch64/RsaKeyGen.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MillerRabin.AArch64 (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.RsaKeyGen.AArch64.Search.code c.call)
      (Spec.RsaKeyGen.primeSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem candidate_noFrames (v : RoundImpl) : (codeWith v.mont.mm v.kernel.run).noFrames = true := by
  simp only [codeWith, kMainWith, loadC, closeCheck, trial, gcdCheck, gcdE, loadE, modLoop, montSetup,
    expSetup, millerRabinWith, mrRoundWith, mrWitness, mrResult, finNone, finUsed, finPrime,
    Impl.Rsa.AArch64.Keys.loadA, trialEntry, halfPass, subA, lowWord, halfCond,
    Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs,
    Impl.Bignum.AArch64.R2Div.choice,
    RoundImpl.kernel, MillerRabin.AArch64.Kernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, ite_true,
    Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | exact v.noFrames | rfl

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := Spec.RsaKeyGen.candidateApi.name ++ v.suffix
  code := codeWith v.mont.mm v.kernel.run
  noFrames := candidate_noFrames v
  correct := VG.Proof.RsaKeyGen.AArch64.sharedCode_correct v.mont v.kernel
  ct := VG.Proof.RsaKeyGen.AArch64.sharedCode_constantTime v.mont v.kernel
    (VG.Proof.RsaKeyGen.AArch64.sharedKMain_ct v.mont v.kernel
      (VG.Proof.RsaKeyGen.AArch64.sharedTail_ct v.mont v.kernel))

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.RsaKeyGen.AArch64.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.RsaKeyGen.primeSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.RsaKeyGen.AArch64.Search
