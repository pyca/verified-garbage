module

public import VerifiedGarbage.TCB.X86.Isa

public import VerifiedGarbage.TCB.Artifact

public import Init.Prelude

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateVerified
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSafety -- shake: keep (the public artifact body uses `code_all`)
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import Init.Core
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Native RSA candidates call every shared i686 Miller–Rabin implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.RsaKeyGen
open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts (v : RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact target {
    suffix := v.suffix
    code := Impl.RsaKeyGen.X86.Candidate.code montName montCode v.name v.code
    stack := 152
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := Proof.RsaKeyGen.X86.Candidate.verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
        v.verified v.noSp v.stack
    spSafe := Proof.RsaKeyGen.X86.Candidate.code_all compact_noSp v.noSp montName v.name
    features := v.features }]

end VG.Generic.MillerRabin.X86.RsaKeyGen
