import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1

/-!
# Deterministic ECDSA over brainpoolP512r1 with HMAC-SHA-512: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP512r1
(`Spec/Ecdsa/BrainpoolP512r1.lean`) with SHA-512:
`vg_ecdsa_brainpoolp512r1_sha512_sign`, in the module `ecdsa_brainpoolp512r1_sha512`.
A candidate is the leftmost 512 bits of `V`, and `n` is well below
`2^512` (`n < 0.667 · 2^512`), so each is unsuitable with probability
about `0.333` (`2^-1.58`): at most 128 candidates, all of which are
unsuitable with probability under `2^-203`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512

/-- brainpoolP512r1 with HMAC-SHA-512. -/
def inst : Instance where
  ecdsa := Ecdsa.BrainpoolP512r1.inst
  hash := Hmac.sha512
  hashLen := 64
  hashName := "sha512"
  hashTitle := "SHA-512"
  tries := 128

/-- `vg_ecdsa_brainpoolp512r1_sha512_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
