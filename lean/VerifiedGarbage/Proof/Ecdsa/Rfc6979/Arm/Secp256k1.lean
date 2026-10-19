module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Secp256k1.Point
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
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Secp256k1.Point
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
public import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
public import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.X25519.Arm.Limbs
public import VerifiedGarbage.Proof.X25519.Field

/-!
# Deterministic ECDSA on 32-bit ARM: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at secp256k1's sizes, which is `Proof.Ecdsa.Arm.Secp256k1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- secp256k1, with the group law `hL`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.Secp256k1.curve = 0; rw [secp256k1_nBits]
  coreN := Spec.Ecdsa.Secp256k1.signApi.name
  coreC := Impl.Ecdsa.Arm.signSecp256k1
  coreX := Proof.Ecdsa.Arm.Secp256k1.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.Secp256k1.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.Arm
