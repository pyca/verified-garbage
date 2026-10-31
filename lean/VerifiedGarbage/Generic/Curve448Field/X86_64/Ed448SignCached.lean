module
import VerifiedGarbage.Proof.Ed448.X86_64.VariantForLit

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAdd
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash
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
public import VerifiedGarbage.Proof.Ed448.X86_64.Words57
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.X448.Bytes
public import VerifiedGarbage.Proof.X448.X86_64.AddSub
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Mul
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
public import VerifiedGarbage.Proof.X448.X86_64.Bits
public import VerifiedGarbage.Proof.X448.X86_64.Freeze
public import VerifiedGarbage.Proof.X448.X86_64.Main
public import VerifiedGarbage.Proof.X448.X86_64.Pow223
public import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
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
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
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
import VerifiedGarbage.Proof.Ed448.X86_64.Words57
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X448.X86_64.Main

/-! # Ed448 signing with a cached public key on x86-64 -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448SignCached

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.signCachedApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Impl.Ed448.X86_64.SignCached.signCachedFor v
    stack := 464
    verified := Proof.Ed448.X86_64.SignCached.signCached_verified
      (Proof.Ed448.X86_64.scalarBaseFor_ok v Proof.Ed448.baseLadder_ok)
      (Proof.Ed448.X86_64.scalarBaseFor_ct v) }]

end VG.Generic.Curve448Field.X86_64.Ed448SignCached
