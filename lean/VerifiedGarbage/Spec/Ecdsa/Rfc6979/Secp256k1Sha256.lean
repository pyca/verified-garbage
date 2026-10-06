import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.Secp256k1

/-!
# Deterministic ECDSA over secp256k1 with HMAC-SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of secp256k1
(`Spec/Ecdsa/Secp256k1.lean`) with SHA-256: `vg_ecdsa_secp256k1_sha256_sign`,
in the module `ecdsa_secp256k1_sha256`. At most 8 candidates: each is
unsuitable with probability under `2^-127` (`n > 2^256 - 2^129`), so all 8
with probability under `2^-1016`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.Secp256k1Sha256

/-- secp256k1 with HMAC-SHA-256. -/
def inst : Instance where
  ecdsa := Ecdsa.Secp256k1.inst
  hash := Hmac.sha256
  hashLen := 32
  hashName := "sha256"
  hashTitle := "SHA-256"
  tries := 8

/-- `vg_ecdsa_secp256k1_sha256_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.Secp256k1Sha256
