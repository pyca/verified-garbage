module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Satisfiable
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime tests call every shared PPC64LE Miller–Rabin round

One function for each candidate size DSA parameter generation tests: q of
160 and 256 bits, p of 1024, 2048 and 3072 bits. -/

@[expose] public section
namespace VG.Generic.MillerRabin.PPC64LE.DsaProbablePrime
open VG VG.PPC64LE VG.Proof.MillerRabin.PPC64LE

def helper (v : RoundImpl) (bits : Nat)
    (verified : Verified target (Impl.Dsa.PPC64LE.ProbablePrime.code bits v.name v.code)
      (Proof.Dsa.PPC64LE.Prime.contract bits)) : Artifact :=
  (Spec.Dsa.ProbablePrime.api (Impl.Dsa.PPC64LE.ProbablePrime.layout bits)).artifact target {
    suffix := v.suffix
    notes := ["The candidate's big-endian octets are loaded into RSA's Montgomery working space of at \
      least four 64-bit words, at byte 552 of `ws`, behind the caller's saved registers. Trial \
      division by the shared table of 32-bit primes and their inverses (Montgomery reduction by \
      2^32 of the candidate's 32-bit digits) returns at the first divisor. `R² mod c` takes \
      `64 + w` modular doublings from `2^(64 (w − 1))` and six Montgomery squares, but for 160 \
      bits, whose top word is zero, `128 w` doublings from 1. The blinded loop draws \
      each witness from the tape, cut to the candidate's width, forces a non-uniform draw into \
      range rather than rejecting it, and calls the shared Miller–Rabin round."]
    code := Impl.Dsa.PPC64LE.ProbablePrime.code bits v.name v.code
    stack := 176
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := verified
    features := v.features }

def artifacts (v : RoundImpl) : List Artifact := [
  helper v 160 (Proof.Dsa.PPC64LE.Prime.verified v 160),
  helper v 256 (Proof.Dsa.PPC64LE.Prime.verified v 256),
  helper v 1024 (Proof.Dsa.PPC64LE.Prime.verified v 1024),
  helper v 2048 (Proof.Dsa.PPC64LE.Prime.verified v 2048),
  helper v 3072 (Proof.Dsa.PPC64LE.Prime.verified v 3072)]

end VG.Generic.MillerRabin.PPC64LE.DsaProbablePrime
