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
