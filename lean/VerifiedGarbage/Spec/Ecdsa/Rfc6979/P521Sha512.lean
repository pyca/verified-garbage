module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Spec.Ecdsa.P521

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-521
(`Spec/Ecdsa/P521.lean`) with SHA-512: `vg_ecdsa_p521_sha512_sign`, in the
module `ecdsa_p521_sha512`. At most 8 candidates: each is unsuitable with
probability under `2^-261` (`n > 2^521 - 2^259`), so all 8 with
probability under `2^-2088`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979.P521Sha512

/-- P-521 with HMAC-SHA-512. -/
def inst : Instance where
  ecdsa := Ecdsa.P521.inst
  hash := Hmac.sha512
  hashLen := 64
  hashName := "sha512"
  hashTitle := "SHA-512"
  tries := 8

/-- `vg_ecdsa_p521_sha512_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.P521Sha512
