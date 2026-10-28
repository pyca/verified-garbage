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
    notes := ["Baseline ARMv7, on the working space of the RSA key routines from byte 384 of `ws`, in \
        32-bit limbs, as the RSA candidate's code: the candidate's bytes loaded, trial division by \
        Montgomery reduction of its 16-bit halves modulo each small prime, then Montgomery \
        multiplication modulo the candidate and each witness, the last `bits / 8` of a draw of \
        whole 64-bit words, fixed under masks, in Montgomery form for a call of the shared \
        `vg_miller_rabin_round`, whose frame takes the 56 bytes below this function's. A 32-byte \
        allocation above the frame holds the arguments that code reads from its frame, and the \
        widths it reads there, which shifts and additions derive from `bits`: one body for every size."]
    code := Impl.Dsa.Arm.ProbablePrime.code v.name v.code
    stack := 144
    verified := Proof.Dsa.Arm.Prime.prime_verified v
    features := v.features }]

end VG.Generic.MillerRabin.Arm.DsaProbablePrime
