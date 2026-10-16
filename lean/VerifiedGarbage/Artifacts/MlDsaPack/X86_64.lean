module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on x86-64: the encodings -/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.X86_64

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.simpleBitPack
    verified := Proof.MlDsa.X86_64.Pack.simpleBitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.bitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.bitPack
    verified := Proof.MlDsa.X86_64.Pack.bitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.bitUnpackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.bitUnpack
    verified := Proof.MlDsa.X86_64.Pack.bitUnpack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.unpackT1Api.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.unpackT1
    verified := Proof.MlDsa.X86_64.Pack.unpackT1_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.hintBitPackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.hintBitPack
    verified := Proof.MlDsa.X86_64.Pack.hintBitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.hintBitUnpackApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Pack.hintBitUnpack
    verified := Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaPack.X86_64
