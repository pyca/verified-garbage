module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1

/-!
# Deterministic ECDSA on PPC64LE: each curve's signature, verified

For each curve, `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (`<curve>_verified`), from its file's
`RfcCurve` and the generic proof (`signT_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

theorem p192T (hL : Weierstrass.Law Spec.P192.curve) : CurveT (p192C hL) Spec.Ecdsa.Rfc6979.Curves.p192 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p192_verified (hL : Weierstrass.Law Spec.P192.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p192C hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 vs) :=
  signT_verified (p192T hL) rfl hO (by decide)

theorem p224T (hL : Weierstrass.Law Spec.P224.curve) : CurveT (p224C hL) Spec.Ecdsa.Rfc6979.Curves.p224 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p224_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p224_verified (hL : Weierstrass.Law Spec.P224.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p224C hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 vs) :=
  signT_verified (p224T hL) rfl hO (by decide)

theorem p256T (hL : Weierstrass.Law Spec.P256.curve) : CurveT (p256C hL) Spec.Ecdsa.Rfc6979.Curves.p256 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p256_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p256_verified (hL : Weierstrass.Law Spec.P256.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p256C hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 vs) :=
  signT_verified (p256T hL) rfl hO (by decide)

theorem p384T (hL : Weierstrass.Law Spec.P384.curve) : CurveT (p384C hL) Spec.Ecdsa.Rfc6979.Curves.p384 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p384_verified (hL : Weierstrass.Law Spec.P384.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p384C hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 vs) :=
  signT_verified (p384T hL) rfl hO (by decide)

theorem p521T (hL : Weierstrass.Law Spec.P521.curve) : CurveT (p521C hL) Spec.Ecdsa.Rfc6979.Curves.p521 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p521_verified (hL : Weierstrass.Law Spec.P521.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (p521C hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 vs) :=
  signT_verified (p521T hL) rfl hO (by decide)

theorem secp256k1T (hL : Weierstrass.Law Spec.Secp256k1.curve) : CurveT (secp256k1C hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem secp256k1_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (secp256k1C hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 vs) :=
  signT_verified (secp256k1T hL) rfl hO (by decide)

theorem brainpoolp256r1T (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : CurveT (brainpoolp256r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp256r1_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (brainpoolp256r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 vs) :=
  signT_verified (brainpoolp256r1T hL) rfl hO (by decide)

theorem brainpoolp384r1T (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : CurveT (brainpoolp384r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp384r1_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (brainpoolp384r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 vs) :=
  signT_verified (brainpoolp384r1T hL) rfl hO (by decide)

theorem brainpoolp512r1T (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : CurveT (brainpoolp512r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 :=
  ⟨rfl, by decide, by decide⟩

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp512r1_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HashTable.PPC64LE.TVar) (hO : OK vs) :
    Verified PPC64LE.target (signCode (brainpoolp512r1C hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 vs) :=
  signT_verified (brainpoolp512r1T hL) rfl hO (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
