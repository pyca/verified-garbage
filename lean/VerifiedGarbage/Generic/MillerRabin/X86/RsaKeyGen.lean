module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateVerified
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSafety
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
import VerifiedGarbage.Proof.Mont.X86.Compact.Verified
public import Init.Core
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Native RSA candidates call every shared i686 Miller–Rabin implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.RsaKeyGen
open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts (v : RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact target {
    suffix := v.suffix
    notes := ["Native paired 32-bit arithmetic with a prepared small-prime inverse table, \
      a whole-word 65537 filter, and a fixed-step general public-exponent filter. \
      Montgomery constants and the four-bit Miller–Rabin window are reused across blinded witnesses. \
      One private call frame supplies the prepared multiplication capacity for the entire test. \
      Distance checks, witness selection, and retry behavior satisfy the shared candidate contract."]
    code := Impl.RsaKeyGen.X86.Candidate.code montName montCode v.name v.code
    stack := 112
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := by
      exact Proof.RsaKeyGen.X86.Candidate.verified Proof.Mont.X86.Compact.verified compact_noSp compact_stack
        v.verified v.noSp v.stack
    spSafe := by exact Code.all_of_allInstrs (Proof.RsaKeyGen.X86.Candidate.code_sp compact_noSp v.noSp montName v.name)
    features := v.features }]

end VG.Generic.MillerRabin.X86.RsaKeyGen
