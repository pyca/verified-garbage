module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1

/-!
# Deterministic ECDSA over brainpoolP256r1 with HMAC-SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP256r1
(`Spec/Ecdsa/BrainpoolP256r1.lean`) with SHA-256:
`vg_ecdsa_brainpoolp256r1_sha256_sign`, in the module `ecdsa_brainpoolp256r1_sha256`.
A candidate is the leftmost 256 bits of `V`, and `n` is well below
`2^256` (`n < 0.664 · 2^256`), so each is unsuitable with probability
about `0.336` (`2^-1.57`): at most 128 candidates, all of which are
unsuitable with probability under `2^-201`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256

/-- brainpoolP256r1 with HMAC-SHA-256. -/
def inst : Instance where
  ecdsa := Ecdsa.BrainpoolP256r1.inst
  hash := Hmac.sha256
  hashLen := 32
  hashName := "sha256"
  hashTitle := "SHA-256"
  tries := 128

/-- `vg_ecdsa_brainpoolp256r1_sha256_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
