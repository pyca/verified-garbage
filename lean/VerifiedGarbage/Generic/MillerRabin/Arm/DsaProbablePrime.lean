module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime tests on ARMv7 call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.DsaProbablePrime

def helper (v : Proof.MillerRabin.Arm.RoundImpl) (bits : Nat)
    (h : Verified Arm.target (Impl.Dsa.Arm.ProbablePrime.code bits v.name v.code)
      (Spec.Dsa.ProbablePrime.contract (Impl.Dsa.Arm.ProbablePrime.layout bits) Arm.abi 144)) : Artifact :=
  (Spec.Dsa.ProbablePrime.api (Impl.Dsa.Arm.ProbablePrime.layout bits)).artifact Arm.target {
    suffix := v.suffix
    notes := ["Baseline ARMv7, on the working space of the RSA key routines from byte 384 of `ws`, in \
        32-bit limbs, as the RSA candidate's code: the candidate's bytes loaded, trial division by \
        Montgomery reduction of its 16-bit halves modulo each small prime, then Montgomery \
        multiplication modulo the candidate and each witness, the last `bits / 8` of a draw of \
        whole 64-bit words, fixed under masks, in Montgomery form for a call of the shared \
        `vg_miller_rabin_round`, whose frame takes the 56 bytes below this function's. A 32-byte \
        allocation above the frame holds the arguments that code reads from its frame."]
    code := Impl.Dsa.Arm.ProbablePrime.code bits v.name v.code
    stack := 144
    verified := h
    features := v.features }

open Proof.Dsa.Arm.Prime in
def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  helper v 160 (prime_verified v 160),
  helper v 256 (prime_verified v 256),
  helper v 1024 (prime_verified v 1024),
  helper v 2048 (prime_verified v 2048),
  helper v 3072 (prime_verified v 3072)]

end VG.Generic.MillerRabin.Arm.DsaProbablePrime
