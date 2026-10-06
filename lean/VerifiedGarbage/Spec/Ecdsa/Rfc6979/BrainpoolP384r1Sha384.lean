import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1

/-!
# Deterministic ECDSA over brainpoolP384r1 with HMAC-SHA-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP384r1
(`Spec/Ecdsa/BrainpoolP384r1.lean`) with SHA-384:
`vg_ecdsa_brainpoolp384r1_sha384_sign`, in the module `ecdsa_brainpoolp384r1_sha384`.
A candidate is the leftmost 384 bits of `V`, and `n` is well below
`2^384` (`n < 0.550 · 2^384`), so each is unsuitable with probability
about `0.450` (`2^-1.15`): at most 128 candidates, all of which are
unsuitable with probability under `2^-147`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384

/-- brainpoolP384r1 with HMAC-SHA-384. -/
def inst : Instance where
  ecdsa := Ecdsa.BrainpoolP384r1.inst
  hash := Hmac.sha384
  hashLen := 48
  hashName := "sha384"
  hashTitle := "SHA-384"
  tries := 128

/-- `vg_ecdsa_brainpoolp384r1_sha384_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
