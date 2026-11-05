module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Main
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTop
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTest
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.TrialOk
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Correct
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.CT
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Implies

/-! # The verified prime search (RISCV64)

For any candidate using at most 288 bytes of stack (`search_verified_of`),
and for the candidate calling each shared Miller–Rabin round
(`search_verified`), as `Generic/MillerRabin/RISCV64/RsaKeyGen.lean`
registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG VG.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Candidate
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.RsaKeyGen.RISCV64.Search.code c.call)
      (Spec.RsaKeyGen.primeSearchContract (abi.withConsts tables) stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses its frame and the stack its round does. -/
theorem candidate_stack (v : RoundImpl) :
    sdepth (code (Impl.RsaKeyGen.RISCV64.Trial.trial hTrial) v.name v.code) ≤ 288 := by
  simp only [code, body, main, test, seqs, Impl.RsaKeyGen.RISCV64.Witness.millerRabin,
    Impl.RsaKeyGen.RISCV64.Witness.draw, Impl.RsaKeyGen.RISCV64.Witness.round,
    Impl.MillerRabin.RISCV64.Search.roundCall, sdepth, Instr.frameBytes, frameBytes]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  have := v.stack
  omega

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.RISCV64.Candidate.code (Impl.RsaKeyGen.RISCV64.Trial.trial hTrial) v.name v.code
  stack := candidate_stack v
  correct := fun _ h₁ h₂ => Cand.code_correct Cand.TrialOk.trial_divOk v h₁ h₂
  ct := Cand.code_rel Cand.TrialOk.trial_divOk v (Cand.main_rel v (Cand.test_ct Cand.TrialOk.trial_divOk v))

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.RsaKeyGen.RISCV64.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.RsaKeyGen.primeSearchContract (abi.withConsts tables) stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.RsaKeyGen.RISCV64.Search
