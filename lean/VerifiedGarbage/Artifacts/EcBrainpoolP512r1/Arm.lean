module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.EcKey.Arm.Finish
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
public import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
public import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
public import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.X25519.Arm.Limbs
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP512r1.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact Arm.target {
    code := Impl.EcKey.Arm.publicKeyBrainpoolP512r1
    verified := Proof.EcKey.Arm.BrainpoolP512r1.pk_verified hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.EcKey.Arm.publicKeyBrainpoolP512r1U
    verified := Proof.EcKey.Arm.BrainpoolP512r1.pkU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcBrainpoolP512r1.Arm
