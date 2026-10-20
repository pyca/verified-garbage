module

public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.Arm.Verify
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
public import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
public import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
public import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
public import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
public import VerifiedGarbage.Proof.X25519.Arm.Pass
public import VerifiedGarbage.Proof.X448.Arm.Carry
public import VerifiedGarbage.Proof.X448.Arm.Copy
public import VerifiedGarbage.Proof.X448.Arm.Counters
public import VerifiedGarbage.Proof.X448.Arm.Decode
public import VerifiedGarbage.Proof.X448.Arm.DecodeAll
public import VerifiedGarbage.Proof.X448.Arm.Fill
public import VerifiedGarbage.Proof.X448.Arm.Finish
public import VerifiedGarbage.Proof.X448.Arm.Init
public import VerifiedGarbage.Proof.X448.Arm.Initial
public import VerifiedGarbage.Proof.X448.Arm.MulLoop
public import VerifiedGarbage.Proof.X448.Arm.Normalize
public import VerifiedGarbage.Proof.X448.Arm.Restore
public import VerifiedGarbage.Proof.X448.Arm.RowPass
public import VerifiedGarbage.Proof.X448.Arm.Setup
public import VerifiedGarbage.Proof.X448.Arm.Step
public import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.X448.Arm.Copy
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.X448.Arm.Decode
import VerifiedGarbage.Proof.X448.Arm.DecodeAll
import VerifiedGarbage.Proof.X448.Arm.Fill
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.X448.Arm.Initial
import VerifiedGarbage.Proof.X448.Arm.MulLoop
import VerifiedGarbage.Proof.X448.Arm.Normalize
import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.RowPass
import VerifiedGarbage.Proof.X448.Arm.Setup
import VerifiedGarbage.Proof.X448.Arm.Step
import VerifiedGarbage.Proof.X448.Bytes

/-!
# Ed448 verification on ARMv7

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_verify_equation` is passed to the caller's here, so that only
this file imports it, with the reference computations' agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.Arm

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact Arm.target {
    notes := ["Uses baseline integer instructions. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, with the Keccak state and the sponge functions' \
      working space in `scratch`) into the frame, reduces the hash modulo L there with \
      `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s result. The frame \
      (the hash and k) is not cleared: verification has no secrets."]
    code := Impl.Ed448.Arm.Verify.code
    stack := 280
    verified := Proof.Ed448.Arm.Verify.verify_verified
      (Proof.Ed448.Arm.verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      Proof.Ed448.Arm.verifyEquation_ct }]

end VG.Artifacts.Ed448Verify.Arm
