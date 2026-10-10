module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Spec.Ecdsa.P224

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-224
(`Spec/Ecdsa/P224.lean`) with SHA-224: `vg_ecdsa_p224_sha224_sign`, in the
module `ecdsa_p224_sha224`. At most 8 candidates: each is unsuitable with
probability under `2^-111` (`n > 2^224 - 2^112`), so all 8 with
probability under `2^-888`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979.P224Sha224

/-- P-224 with HMAC-SHA-224. -/
def inst : Instance where
  ecdsa := Ecdsa.P224.inst
  hash := Hmac.sha224
  hashLen := 28
  hashName := "sha224"
  hashTitle := "SHA-224"
  tries := 8

/-- `vg_ecdsa_p224_sha224_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.P224Sha224
