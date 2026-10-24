module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly

/-! # ML-DSA (FIPS 204) on x86-64: the encodings -/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.X86_64

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.simpleBitPack
    verified := Proof.MlDsa.X86_64.Pack.simpleBitPack_verified },
  Spec.MlDsa.bitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.bitPack
    verified := Proof.MlDsa.X86_64.Pack.bitPack_verified },
  Spec.MlDsa.bitUnpackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.bitUnpack
    verified := Proof.MlDsa.X86_64.Pack.bitUnpack_verified },
  Spec.MlDsa.unpackT1Api.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.unpackT1
    verified := Proof.MlDsa.X86_64.Pack.unpackT1_verified },
  Spec.MlDsa.hintBitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.hintBitPack
    verified := Proof.MlDsa.X86_64.Pack.hintBitPack_verified },
  Spec.MlDsa.hintBitUnpackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.hintBitUnpack
    verified := Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified }]

end VG.Artifacts.MlDsaPack.X86_64
