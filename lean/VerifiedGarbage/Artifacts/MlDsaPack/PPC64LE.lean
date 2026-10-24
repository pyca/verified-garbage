module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintPackCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintUnpackCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: the encodings -/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.simpleBitPack
    verified := Proof.MlDsa.PPC64LE.Pack.simpleBitPack_verified },
  Spec.MlDsa.bitPackApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.bitPack
    verified := Proof.MlDsa.PPC64LE.Pack.bitPack_verified },
  Spec.MlDsa.bitUnpackApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.bitUnpack
    verified := Proof.MlDsa.PPC64LE.Pack.bitUnpack_verified },
  Spec.MlDsa.unpackT1Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.unpackT1
    verified := Proof.MlDsa.PPC64LE.Pack.unpackT1_verified },
  Spec.MlDsa.hintBitPackApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.hintBitPack
    verified := Proof.MlDsa.PPC64LE.Pack.hintBitPack_verified },
  Spec.MlDsa.hintBitUnpackApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Pack.hintBitUnpack
    verified := Proof.MlDsa.PPC64LE.Pack.hintBitUnpack_verified }]

end VG.Artifacts.MlDsaPack.PPC64LE
