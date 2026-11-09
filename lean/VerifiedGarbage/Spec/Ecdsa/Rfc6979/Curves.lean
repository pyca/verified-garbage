module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1

/-!
# Deterministic ECDSA with its HMAC given as a table: each curve

**Trusted** (as every file in `Spec/`). The `TableInstance` of each curve:
its `vg_ecdsa_<curve>_sign`, in the module `ecdsa_<curve>`, and its bound
on candidates. The bound depends only on the curve: a candidate is the
leftmost `qlen` bits of HMAC outputs, and whether it is suitable depends
on how close `n` is to `2^qlen`, not on the hash function.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979.Curves

open Rfc6979 (TableInstance)

/-- P-192 (`Spec/Ecdsa/P192.lean`): `vg_ecdsa_p192_sign`, in the module
`ecdsa_p192`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-96`
(`n > 2^192 - 2^95`), so all 8 with probability under `2^-768`. -/
def p192 : TableInstance where
  ecdsa := Ecdsa.P192.inst
  tries := 8

/-- `vg_ecdsa_p192_sign` on every target. -/
def p192SignApi : Api := p192.signApi

/-- P-224 (`Spec/Ecdsa/P224.lean`): `vg_ecdsa_p224_sign`, in the module
`ecdsa_p224`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-111`
(`n > 2^224 - 2^112`), so all 8 with probability under `2^-888`. -/
def p224 : TableInstance where
  ecdsa := Ecdsa.P224.inst
  tries := 8

/-- `vg_ecdsa_p224_sign` on every target. -/
def p224SignApi : Api := p224.signApi

/-- P-256 (`Spec/Ecdsa/P256.lean`): `vg_ecdsa_p256_sign`, in the module
`ecdsa_p256`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-31`
(`n > 2^256 - 2^224`), so all 8 with probability under `2^-248`. -/
def p256 : TableInstance where
  ecdsa := Ecdsa.P256.inst
  tries := 8

/-- `vg_ecdsa_p256_sign` on every target. -/
def p256SignApi : Api := p256.signApi

/-- P-384 (`Spec/Ecdsa/P384.lean`): `vg_ecdsa_p384_sign`, in the module
`ecdsa_p384`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-193`
(`n > 2^384 - 2^190`), so all 8 with probability under `2^-1544`. -/
def p384 : TableInstance where
  ecdsa := Ecdsa.P384.inst
  tries := 8

/-- `vg_ecdsa_p384_sign` on every target. -/
def p384SignApi : Api := p384.signApi

/-- P-521 (`Spec/Ecdsa/P521.lean`): `vg_ecdsa_p521_sign`, in the module
`ecdsa_p521`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-261`
(`n > 2^521 - 2^259`), so all 8 with probability under `2^-2088`. -/
def p521 : TableInstance where
  ecdsa := Ecdsa.P521.inst
  tries := 8

/-- `vg_ecdsa_p521_sign` on every target. -/
def p521SignApi : Api := p521.signApi

/-- secp256k1 (`Spec/Ecdsa/Secp256k1.lean`): `vg_ecdsa_secp256k1_sign`, in the
module `ecdsa_secp256k1`. At most 8 candidates whatever the hash function: each is
unsuitable with probability under `2^-127`
(`n > 2^256 - 2^129`), so all 8 with probability under `2^-1016`. -/
def secp256k1 : TableInstance where
  ecdsa := Ecdsa.Secp256k1.inst
  tries := 8

/-- `vg_ecdsa_secp256k1_sign` on every target. -/
def secp256k1SignApi : Api := secp256k1.signApi

/-- brainpoolP256r1 (`Spec/Ecdsa/BrainpoolP256r1.lean`):
`vg_ecdsa_brainpoolp256r1_sign`, in the module `ecdsa_brainpoolp256r1`. At
most 128 candidates whatever the hash function: a
candidate is the leftmost 256 bits of `V`, and `n < 0.664 · 2^256`, so each
is unsuitable with probability about `0.336` (`2^-1.57`), and all 128 with
probability under `2^-201`. -/
def brainpoolp256r1 : TableInstance where
  ecdsa := Ecdsa.BrainpoolP256r1.inst
  tries := 128

/-- `vg_ecdsa_brainpoolp256r1_sign` on every target. -/
def brainpoolp256r1SignApi : Api := brainpoolp256r1.signApi

/-- brainpoolP384r1 (`Spec/Ecdsa/BrainpoolP384r1.lean`):
`vg_ecdsa_brainpoolp384r1_sign`, in the module `ecdsa_brainpoolp384r1`. At
most 128 candidates whatever the hash function: a
candidate is the leftmost 384 bits of `V`, and `n < 0.550 · 2^384`, so each
is unsuitable with probability about `0.450` (`2^-1.15`), and all 128 with
probability under `2^-147`. -/
def brainpoolp384r1 : TableInstance where
  ecdsa := Ecdsa.BrainpoolP384r1.inst
  tries := 128

/-- `vg_ecdsa_brainpoolp384r1_sign` on every target. -/
def brainpoolp384r1SignApi : Api := brainpoolp384r1.signApi

/-- brainpoolP512r1 (`Spec/Ecdsa/BrainpoolP512r1.lean`):
`vg_ecdsa_brainpoolp512r1_sign`, in the module `ecdsa_brainpoolp512r1`. At
most 128 candidates whatever the hash function: a
candidate is the leftmost 512 bits of `V`, and `n < 0.667 · 2^512`, so each
is unsuitable with probability about `0.333` (`2^-1.58`), and all 128 with
probability under `2^-203`. -/
def brainpoolp512r1 : TableInstance where
  ecdsa := Ecdsa.BrainpoolP512r1.inst
  tries := 128

/-- `vg_ecdsa_brainpoolp512r1_sign` on every target. -/
def brainpoolp512r1SignApi : Api := brainpoolp512r1.signApi

end VG.Spec.Ecdsa.Rfc6979.Curves
