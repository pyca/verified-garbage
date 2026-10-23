module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Spec.Dsa.ProbablePrime
public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Verified
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime tests call every shared i686 Miller–Rabin implementation

One function for each candidate size DSA parameter generation tests: q of
160 and 256 bits, p of 1024, 2048 and 3072 bits. -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.DsaProbablePrime
open VG VG.X86 VG.Proof.MillerRabin.X86

def helper (v : RoundImpl) (bits : Nat)
    (verified : Verified target (Impl.Dsa.X86.ProbablePrime.code bits montName montCode v.name v.code)
      (Proof.Dsa.X86.ProbablePrime.contract bits)) : Artifact :=
  (Spec.Dsa.ProbablePrime.api (Impl.Dsa.X86.ProbablePrime.layout bits)).artifact target {
    suffix := v.suffix
    notes := ["RSA's i686 candidate machinery on a given candidate: its big-endian octets are \
      imported into a Montgomery workspace of at least four 64-bit words, sieved with the prepared \
      small-prime inverse table, and tested by the blinded loop with the shared Miller–Rabin round, \
      witnesses cut to the candidate's width. One private call frame supplies the prepared \
      multiplication capacity for the entire test."]
    code := Impl.Dsa.X86.ProbablePrime.code bits montName montCode v.name v.code
    stack := 152
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := verified
    spSafe := Proof.Dsa.X86.ProbablePrime.code_all compact_noSp v.noSp bits montName v.name
    features := v.features }

open Proof.Dsa.X86.ProbablePrime in
def artifacts (v : RoundImpl) : List Artifact := [
  helper v 160 (verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack 160),
  helper v 256 (verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack 256),
  helper v 1024 (verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack 1024),
  helper v 2048 (verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack 2048),
  helper v 3072 (verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack 3072)]

end VG.Generic.MillerRabin.X86.DsaProbablePrime
