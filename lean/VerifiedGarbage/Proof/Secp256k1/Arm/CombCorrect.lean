module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Secp256k1.Arm.CombLayout
import VerifiedGarbage.Proof.Secp256k1.Comb7
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.Arm.MontSecp256k1
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The checked seven-bit secp256k1 comb satisfies the full scalar-multiplication proof. -/

@[expose] public section
namespace VG.Proof.Secp256k1.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Secp256k1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_config (hC : Law Spec.Secp256k1.curve) (u : Bool := false) :
    Config (secp256k1CombWith u) Spec.Secp256k1.curve secp256k1Comb7 secp256k1Comb7Start where
  layout := comb_layout u
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.secp256k1p_ok
  unit := unitMod_pow_two (by decide +kernel +revert) _
  tables := combOk7 hC VG.Proof.Secp256k1.onCurve_G
  one_lt := by decide +kernel +revert
  one := toM_one (unitMod_pow_two (by decide +kernel +revert) _)
  startX := rfl
  startY := rfl
  w1 := by decide +revert
  w9 := by decide +revert
  J1 := by decide +revert
  J32 := by decide +revert
  startBits := by decide +revert
  coverBits := by decide +revert
  bitsLow := by decide +revert
  bitsHigh := by decide +revert
  bitsFit := by decide +revert
  windowFit := by decide +revert
  encJ := by decide +revert
  encLast := by decide +revert
  encRow := by decide +revert
  encEntry := by decide +revert
  encH := by decide +revert

end VG.Proof.Secp256k1.Arm
