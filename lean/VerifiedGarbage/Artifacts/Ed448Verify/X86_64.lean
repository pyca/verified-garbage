module

import VerifiedGarbage.Proof.Ed448.X86_64.VariantForLit
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86_64.Verify
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.X448.X86_64.Main
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Curve448Field.X86_64

/-! # Ed448 verification on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.X86_64

def artifactsFor (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.verifyApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Impl.Ed448.X86_64.Verify.verifyFor v
    stack := 272
    verified := Proof.Ed448.X86_64.Verify.verify_verified
      (Proof.Ed448.X86_64.verifyEquationFor_ok v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      (Proof.Ed448.X86_64.verifyEquationFor_ct v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Curve448Field.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448Verify.X86_64
