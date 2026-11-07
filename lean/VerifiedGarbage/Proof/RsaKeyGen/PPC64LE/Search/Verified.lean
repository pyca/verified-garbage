module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Search
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Body
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTTop
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.TrialOk
public import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Correct
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.CT
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Implies

/-! # The verified prime search (PPC64LE)

For any candidate using at most 400 bytes of stack (`search_verified_of`),
and for the candidate calling each shared Miller–Rabin round
(`search_verified`), as `Generic/MillerRabin/PPC64LE/RsaKeyGen.lean`
registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG VG.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.RsaKeyGen.PPC64LE.Search.code c.call)
      (Proof.RsaKeyGen.primeSearchContract (abi.withConsts tables) stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses its push, its frame and the stack its round does. -/
theorem candidate_stack (v : RoundImpl) :
    sdepth (code (Impl.RsaKeyGen.PPC64LE.Trial.trial hTrial) v.name v.code) ≤ 400 := by
  simp only [code, body, main, test, seqs, Impl.RsaKeyGen.PPC64LE.Witness.millerRabin,
    Impl.RsaKeyGen.PPC64LE.Witness.draw, Impl.RsaKeyGen.PPC64LE.Witness.round,
    Impl.MillerRabin.PPC64LE.Search.roundCall, sdepth, Instr.frameBytes, frameBytes]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  have := v.stack
  omega

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.PPC64LE.Candidate.code (Impl.RsaKeyGen.PPC64LE.Trial.trial hTrial) v.name v.code
  stack := candidate_stack v
  correct := fun _ h₁ h₂ => Cand.code_correct Cand.TrialOk.trial_divOk v h₁ h₂
  ct := Cand.code_ct Cand.TrialOk.trial_divOk v

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.RsaKeyGen.PPC64LE.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Proof.RsaKeyGen.primeSearchContract (abi.withConsts tables) stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.RsaKeyGen.PPC64LE.Search
