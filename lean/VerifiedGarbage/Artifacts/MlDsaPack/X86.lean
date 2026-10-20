module

public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackEnd
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackLoop
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackMain
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackLoop
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackMain

/-!
# ML-DSA (FIPS 204) on x86: the encodings

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.X86

def artifacts : List Artifact := [
  Spec.MlDsa.simpleBitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.simpleBitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.SimpleBitPack.verified },
  Spec.MlDsa.bitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.bitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.BitPack.verified },
  Spec.MlDsa.bitUnpackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.bitUnpack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.BU.verified },
  Spec.MlDsa.unpackT1Api.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.unpackT1
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.T1.verified },
  Spec.MlDsa.hintBitPackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.hintBitPack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Hint.hintBitPack_verified },
  Spec.MlDsa.hintBitUnpackApi.artifact X86.target {
    code := Impl.MlDsa.X86.Pack.hintBitUnpack
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Hint.hintBitUnpack_verified }]

end VG.Artifacts.MlDsaPack.X86
