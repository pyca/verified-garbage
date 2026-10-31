module
import VerifiedGarbage.Proof.Ed448.X86_64.VariantForLit

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
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
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
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
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X448.X86_64.Main

/-! # Ed448 verification on x86-64 -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448Verify

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.verifyApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Impl.Ed448.X86_64.Verify.verifyFor v
    stack := 272
    verified := Proof.Ed448.X86_64.Verify.verify_verified
      (Proof.Ed448.X86_64.verifyEquationFor_ok v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      (Proof.Ed448.X86_64.verifyEquationFor_ct v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok) }]

end VG.Generic.Curve448Field.X86_64.Ed448Verify
