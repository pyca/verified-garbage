module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.Arm.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Row
meta import VerifiedGarbage.Proof.Mont.Arm.Step
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Const
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
meta import VerifiedGarbage.Proof.Weierstrass.Pow
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Limbs
meta import VerifiedGarbage.Proof.X25519.Field

/-!
# Deterministic ECDSA on 32-bit ARM: P-384

P-384 as the proof's curve (`p384`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-384's sizes, which is `Proof.Ecdsa.Arm.P384.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-384, with the group law `hL`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := Spec.Ecdsa.P384.signApi.name
  coreC := Impl.Ecdsa.Arm.signP384
  coreX := Proof.Ecdsa.Arm.P384.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.P384.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.Arm
