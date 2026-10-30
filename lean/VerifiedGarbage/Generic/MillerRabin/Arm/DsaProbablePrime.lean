module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime test on ARMv7 calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.DsaProbablePrime

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  (Spec.Dsa.ProbablePrime.sizedApi Impl.Dsa.Arm.ProbablePrime.layout Impl.Dsa.Arm.ProbablePrime.sizes).artifact
      Arm.target {
    suffix := v.suffix
    code := Impl.Dsa.Arm.ProbablePrime.code v.name v.code
    stack := 144
    verified := Proof.Dsa.Arm.Prime.prime_verified v
    features := v.features }]

end VG.Generic.MillerRabin.Arm.DsaProbablePrime
