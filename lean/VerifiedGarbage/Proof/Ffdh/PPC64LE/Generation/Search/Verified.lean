module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Contract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Verified
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Implies
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode

/-! # The verified parameter search (PPC64LE)

For any candidate using at most 176 bytes of stack (`search_verified_of`),
and for the candidate calling each shared Miller–Rabin round
(`search_verified`), as `Generic/MillerRabin/PPC64LE/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Impl.MillerRabin.PPC64LE.Search (millerRabin draw round roundCall)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.Ffdh.PPC64LE.Generation.Search.code c.call)
      (Spec.Ffdh.parameterSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses the stack its round does. -/
theorem candidate_stack (v : RoundImpl) : sdepth (code v.name v.code) ≤ 176 := by
  simp only [code, main, tests, test, millerRabin, draw, round, roundCall, pResult, qResult, ite_true, ite_false,
    Bool.false_eq_true, sdepth]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  exact v.stack

/-- `vg_ffdh_parameter_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate" ++ v.suffix
  code := Impl.Ffdh.PPC64LE.ParameterCandidate.code v.name v.code
  stack := candidate_stack v
  correct := ParameterCandidate.code_correct v
  ct := ParameterCandidate.code_ct v

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.Ffdh.PPC64LE.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.Ffdh.parameterSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.Ffdh.PPC64LE.Generation
