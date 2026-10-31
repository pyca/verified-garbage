module

public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream

/-! # ML-DSA (FIPS 204) on 32-bit ARM: the encodings -/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.Arm

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.simpleBitPack
    verified := Proof.MlDsa.Arm.Pack.simpleBitPack_verified },
  Spec.MlDsa.bitPackApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.bitPack
    stack := 4
    verified := Proof.MlDsa.Arm.Pack.bitPack_verified },
  Spec.MlDsa.bitUnpackApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.bitUnpack
    stack := 4
    verified := Proof.MlDsa.Arm.Pack.bitUnpack_verified },
  Spec.MlDsa.unpackT1Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.unpackT1
    verified := Proof.MlDsa.Arm.Pack.unpackT1_verified },
  Spec.MlDsa.hintBitPackApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.hintBitPack
    stack := 8
    verified := Proof.MlDsa.Arm.Pack.Hint.hintBitPack_verified },
  Spec.MlDsa.hintBitUnpackApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Pack.hintBitUnpack
    stack := 16
    verified := Proof.MlDsa.Arm.Pack.Hint.hintBitUnpack_verified }]

end VG.Artifacts.MlDsaPack.Arm
